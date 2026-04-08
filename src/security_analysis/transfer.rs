use crate::security_analysis::{
    cfg::build_cfg,
    domain::{
        AbstractState, BitFacts, ConstraintOp, FormulaFacts, FormulaTag, Interval, PathFact,
        RiskKind, RiskOrigin, SymbolicTerm, ValueState, builtin_width, formula_tags_from_name,
        integer_value, low_mask, type_builtin, type_interval, uint_max, width_mask,
    },
    report::{SecurityFinding, SinkKind, collect_diagnostics, normalize_findings},
    rules::{
        fake_checked_shift::guard_is_weaker_than_threshold,
        narrow_cast::cast_max,
        shift_truncation::no_truncation_threshold,
    },
    sinks::{looks_like_financial_name, looks_like_helper, looks_like_sink_call, sink_priority},
    summaries::{FunctionSummary, ReturnSummary},
};
use move_compiler::{
    cfgir::{ast as G, cfg::CFG},
    diagnostics::{Diagnostics, codes::Severity},
    expansion::ast::ModuleIdent,
    hlir::ast as H,
    parser::ast::{BinOp_, FunctionName, UnaryOp_},
};
use move_core_types::u256::U256;
use move_ir_types::location::Loc;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FunctionKey {
    module: ModuleIdent,
    name: FunctionName,
}

#[derive(Clone)]
struct FunctionInfo<'a> {
    key: FunctionKey,
    function: &'a G::Function,
}

#[derive(Clone, Debug)]
struct AnalysisOutcome {
    returns: Vec<ValueState>,
    findings: Vec<SecurityFinding>,
}

impl AnalysisOutcome {
    fn new() -> Self {
        Self {
            returns: vec![],
            findings: vec![],
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AnalysisMode {
    Summary,
    Findings,
}

#[derive(Clone, Copy)]
enum BitwiseOp {
    And,
    Or,
    Xor,
}

pub struct ProgramAnalyzer<'a> {
    functions: BTreeMap<FunctionKey, FunctionInfo<'a>>,
}

impl<'a> ProgramAnalyzer<'a> {
    pub fn new(program: &'a G::Program) -> Self {
        let mut functions = BTreeMap::new();
        for (module, module_def) in program.modules.key_cloned_iter() {
            for (function_name, function) in module_def.functions.key_cloned_iter() {
                functions.insert(
                    FunctionKey {
                        module,
                        name: function_name,
                    },
                    FunctionInfo {
                        key: FunctionKey {
                            module,
                            name: function_name,
                        },
                        function,
                    },
                );
            }
        }
        Self { functions }
    }

    pub fn run(&self) -> Diagnostics {
        collect_diagnostics(self.run_findings())
    }

    pub fn run_findings(&self) -> Vec<SecurityFinding> {
        let summaries = self.compute_summaries();
        let mut findings = vec![];
        for info in self.functions.values() {
            let mut analyzer = FunctionAnalyzer::new(info.clone(), &summaries);
            let outcome = analyzer.analyze(AnalysisMode::Findings);
            findings.extend(outcome.findings);
        }
        normalize_findings(findings)
    }

    fn compute_summaries(&self) -> BTreeMap<FunctionKey, FunctionSummary> {
        let mut summaries = self
            .functions
            .keys()
            .cloned()
            .map(|key| (key, FunctionSummary::empty()))
            .collect::<BTreeMap<_, _>>();
        for _ in 0..6 {
            let mut changed = false;
            let mut next = summaries.clone();
            for (key, info) in &self.functions {
                let mut analyzer = FunctionAnalyzer::new(info.clone(), &summaries);
                let outcome = analyzer.analyze(AnalysisMode::Summary);
                let summary = FunctionSummary {
                    returns: outcome
                        .returns
                        .into_iter()
                        .map(|value| ReturnSummary {
                            parameter_dependencies: value.parameter_dependencies,
                            risky_origins: value.risky_origins,
                        })
                        .collect(),
                };
                if next.get(key) != Some(&summary) {
                    next.insert(key.clone(), summary);
                    changed = true;
                }
            }
            summaries = next;
            if !changed {
                break;
            }
        }
        summaries
    }
}

struct FunctionAnalyzer<'a> {
    info: FunctionInfo<'a>,
    summaries: &'a BTreeMap<FunctionKey, FunctionSummary>,
    local_types: BTreeMap<H::Var, H::Type>,
    current_outcome: AnalysisOutcome,
    mode: AnalysisMode,
}

impl<'a> FunctionAnalyzer<'a> {
    fn new(
        info: FunctionInfo<'a>,
        summaries: &'a BTreeMap<FunctionKey, FunctionSummary>,
    ) -> Self {
        let mut local_types = BTreeMap::new();
        for (_, var, single_ty) in &info.function.signature.parameters {
            local_types.insert(*var, single_to_type(single_ty));
        }
        if let G::FunctionBody_::Defined { locals, .. } = &info.function.body.value {
            for (var, (_, ty)) in locals.key_cloned_iter() {
                local_types.insert(var, single_to_type(ty));
            }
        }
        Self {
            info,
            summaries,
            local_types,
            current_outcome: AnalysisOutcome::new(),
            mode: AnalysisMode::Summary,
        }
    }

    fn analyze(&mut self, mode: AnalysisMode) -> AnalysisOutcome {
        self.mode = mode;
        self.current_outcome = AnalysisOutcome::new();
        let Some((cfg, blocks, _)) = build_cfg(self.info.function) else {
            return self.current_outcome.clone();
        };
        let entry = cfg.start_block();
        let in_states = BTreeMap::from([(entry, self.initial_state())]);
        let mut out_states: BTreeMap<H::Label, AbstractState> = BTreeMap::new();
        let mut worklist = VecDeque::from([entry]);

        while let Some(label) = worklist.pop_front() {
            let mut state_in = in_states
                .get(&label)
                .cloned()
                .unwrap_or_else(AbstractState::new);

            let predecessors = cfg.predecessors(label).clone();
            if !predecessors.is_empty() {
                let mut merged: Option<AbstractState> = None;
                for predecessor in predecessors {
                    let Some(pred_state) = out_states.get(&predecessor) else {
                        continue;
                    };
                    let refined = self.refine_edge(predecessor, label, pred_state, blocks);
                    merged = Some(match merged {
                        Some(existing) => existing.join(&refined),
                        None => refined,
                    });
                }
                if let Some(merged) = merged {
                    state_in = merged;
                }
            }

            let mut current = state_in.clone();
            if current.unreachable {
                out_states.insert(label, current);
                continue;
            }
            let block = blocks.get(&label).expect("existing block");
            for command in block {
                self.execute_command(command, &mut current);
                if current.unreachable {
                    break;
                }
            }

            let changed = out_states.get(&label) != Some(&current);
            out_states.insert(label, current.clone());
            if changed {
                for successor in cfg.successors(label).iter().copied() {
                    worklist.push_back(successor);
                }
            }
        }

        self.current_outcome.clone()
    }

    fn initial_state(&self) -> AbstractState {
        let mut state = AbstractState::new();
        for (index, (_, var, ty)) in self.info.function.signature.parameters.iter().enumerate() {
            let mut value = type_interval(&single_to_type(ty));
            value.term = SymbolicTerm::Var(*var);
            value.parameter_dependencies.insert(index);
            self.annotate_value_with_name(&mut value, &var.value().to_string());
            state.locals.insert(*var, value);
        }
        state
    }

    fn execute_command(&mut self, command: &H::Command, state: &mut AbstractState) {
        use H::Command_ as C;
        match &command.value {
            C::Assign(_, lvalues, exp) => {
                let values = self.eval_exp(exp, state);
                for (index, lvalue) in lvalues.iter().enumerate() {
                    let value = values.get(index).cloned().unwrap_or_else(ValueState::top);
                    self.assign_lvalue(lvalue, value, state);
                }
            }
            C::Mutate(target, value) => {
                let rhs_values = self.eval_exp(value, state);
                let rhs = rhs_values.first().cloned().unwrap_or_else(ValueState::top);
                if let Some((field_loc, field_name)) = self.borrow_field_name(target)
                    && !rhs.risky_origins.is_empty()
                    && looks_like_financial_name(&field_name)
                {
                    for origin in rhs.risky_origins {
                        self.emit_sink(
                            &origin,
                            field_loc,
                            SinkKind::FieldWrite,
                            true,
                            state,
                            Some(self.describe_exp(target)),
                        );
                    }
                }
                let _ = self.eval_exp(target, state);
            }
            C::Return { exp, .. } => {
                let values = self.eval_exp(exp, state);
                self.record_returns(&values);
                if self.is_publicish() {
                    let function_financial = looks_like_financial_name(&self.info.key.name.to_string());
                    for value in values {
                        for origin in value.risky_origins {
                            self.emit_sink(
                                &origin,
                                command.loc,
                                SinkKind::PublicReturn,
                                function_financial,
                                state,
                                Some(format!(
                                    "returned from {}::{}",
                                    self.info.key.module,
                                    self.info.key.name
                                )),
                            );
                        }
                    }
                }
            }
            C::Abort(_, exp) => {
                let _ = self.eval_exp(exp, state);
            }
            C::IgnoreAndPop { exp, .. } => {
                let _ = self.eval_exp(exp, state);
            }
            C::JumpIf { cond, .. } => {
                let _ = self.eval_exp(cond, state);
            }
            C::Jump { .. } | C::VariantSwitch { .. } => {}
            C::Break(_) | C::Continue(_) => {}
        }
    }

    fn record_returns(&mut self, values: &[ValueState]) {
        for (index, value) in values.iter().enumerate() {
            if let Some(existing) = self.current_outcome.returns.get(index).cloned() {
                self.current_outcome.returns[index] = existing.join(value);
            } else {
                self.current_outcome.returns.push(value.clone());
            }
        }
    }

    fn refine_edge(
        &self,
        predecessor: H::Label,
        successor: H::Label,
        state: &AbstractState,
        blocks: &G::BasicBlocks,
    ) -> AbstractState {
        let mut next = state.clone();
        let Some(command) = blocks
            .get(&predecessor)
            .and_then(|block| block.back())
        else {
            return next;
        };
        let H::Command_::JumpIf {
            cond,
            if_true,
            if_false,
        } = &command.value
        else {
            return next;
        };
        if successor == *if_true {
            self.apply_condition(cond, true, &mut next);
        } else if successor == *if_false {
            self.apply_condition(cond, false, &mut next);
        }
        next
    }

    fn apply_condition(&self, exp: &H::Exp, truthy: bool, state: &mut AbstractState) {
        if state.unreachable {
            return;
        }
        if let Some(constraints) = self.collect_constraints(exp, truthy, state) {
            for (var, op, bound, text) in constraints {
                self.apply_constraint(var, op, bound, text, state);
                if state.unreachable {
                    break;
                }
            }
        }
    }

    fn collect_constraints(
        &self,
        exp: &H::Exp,
        truthy: bool,
        state: &AbstractState,
    ) -> Option<Vec<(H::Var, ConstraintOp, U256, String)>> {
        match &exp.exp.value {
            H::UnannotatedExp_::UnaryExp(sp!(_, UnaryOp_::Not), inner) => {
                self.collect_constraints(inner, !truthy, state)
            }
            H::UnannotatedExp_::BinopExp(lhs, op, rhs) => match op.value {
                BinOp_::And if truthy => {
                    let mut constraints = self.collect_constraints(lhs, true, state).unwrap_or_default();
                    constraints.extend(self.collect_constraints(rhs, true, state).unwrap_or_default());
                    Some(constraints)
                }
                BinOp_::And if !truthy => self.merge_disjunctive_constraints(
                    self.collect_constraints(lhs, false, state)?,
                    self.collect_constraints(rhs, false, state)?,
                ),
                BinOp_::Or if truthy => self.merge_disjunctive_constraints(
                    self.collect_constraints(lhs, true, state)?,
                    self.collect_constraints(rhs, true, state)?,
                ),
                BinOp_::Or if !truthy => {
                    let mut constraints = self.collect_constraints(lhs, false, state).unwrap_or_default();
                    constraints.extend(self.collect_constraints(rhs, false, state).unwrap_or_default());
                    Some(constraints)
                }
                BinOp_::Lt | BinOp_::Le | BinOp_::Gt | BinOp_::Ge | BinOp_::Eq | BinOp_::Neq => self
                    .comparison_constraint(lhs, op.value, rhs, truthy, state)
                    .map(|constraint| vec![constraint]),
                _ => None,
            },
            _ => None,
        }
    }

    fn merge_disjunctive_constraints(
        &self,
        left: Vec<(H::Var, ConstraintOp, U256, String)>,
        right: Vec<(H::Var, ConstraintOp, U256, String)>,
    ) -> Option<Vec<(H::Var, ConstraintOp, U256, String)>> {
        if left.len() != 1 || right.len() != 1 {
            return None;
        }
        let (left_var, left_op, left_bound, _) = left[0].clone();
        let (right_var, right_op, right_bound, _) = right[0].clone();
        if left_var != right_var {
            return None;
        }

        let left_interval = self.constraint_interval(&left_op, left_bound)?;
        let right_interval = self.constraint_interval(&right_op, right_bound)?;

        if left_interval.lower.is_none() && right_interval.lower.is_none() {
            let upper = left_interval.upper?.max(right_interval.upper?);
            return Some(vec![(
                left_var,
                ConstraintOp::Le,
                upper,
                format!("{} <= {}", left_var.value(), upper),
            )]);
        }

        if left_interval.upper.is_none() && right_interval.upper.is_none() {
            let lower = left_interval.lower?.min(right_interval.lower?);
            return Some(vec![(
                left_var,
                ConstraintOp::Ge,
                lower,
                format!("{} >= {}", left_var.value(), lower),
            )]);
        }

        if let Some(merged) = self.merge_bounded_with_one_sided(left_var, &left_interval, &right_interval) {
            return Some(vec![merged]);
        }
        if let Some(merged) = self.merge_bounded_with_one_sided(left_var, &right_interval, &left_interval) {
            return Some(vec![merged]);
        }
        if let Some(merged) = self.merge_overlapping_bounded(left_var, &left_interval, &right_interval) {
            return Some(vec![merged]);
        }

        None
    }

    fn merge_bounded_with_one_sided(
        &self,
        var: H::Var,
        bounded: &Interval,
        one_sided: &Interval,
    ) -> Option<(H::Var, ConstraintOp, U256, String)> {
        if let (Some(lower), Some(upper)) = (bounded.lower, bounded.upper) {
            if one_sided.lower.is_none()
                && let Some(other_upper) = one_sided.upper
                && lower <= other_upper
            {
                let merged_upper = upper.max(other_upper);
                return Some((
                    var,
                    ConstraintOp::Le,
                    merged_upper,
                    format!("{} <= {}", var.value(), merged_upper),
                ));
            }
            if one_sided.upper.is_none()
                && let Some(other_lower) = one_sided.lower
                && upper >= other_lower
            {
                let merged_lower = lower.min(other_lower);
                return Some((
                    var,
                    ConstraintOp::Ge,
                    merged_lower,
                    format!("{} >= {}", var.value(), merged_lower),
                ));
            }
        }
        None
    }

    fn merge_overlapping_bounded(
        &self,
        var: H::Var,
        left: &Interval,
        right: &Interval,
    ) -> Option<(H::Var, ConstraintOp, U256, String)> {
        let (Some(left_lower), Some(left_upper), Some(right_lower), Some(right_upper)) =
            (left.lower, left.upper, right.lower, right.upper)
        else {
            return None;
        };

        if left_upper < right_lower || right_upper < left_lower {
            return None;
        }

        let merged_lower = left_lower.min(right_lower);
        let merged_upper = left_upper.max(right_upper);
        if merged_lower == U256::zero() {
            return Some((
                var,
                ConstraintOp::Le,
                merged_upper,
                format!("{} <= {}", var.value(), merged_upper),
            ));
        }

        let max = uint_max(256);
        if merged_upper == max {
            return Some((
                var,
                ConstraintOp::Ge,
                merged_lower,
                format!("{} >= {}", var.value(), merged_lower),
            ));
        }

        None
    }

    fn constraint_interval(&self, op: &ConstraintOp, bound: U256) -> Option<Interval> {
        let max = uint_max(256);
        Some(match op {
            ConstraintOp::Lt => {
                if bound == U256::zero() {
                    Interval::bottom()
                } else {
                    Interval {
                        lower: Some(U256::zero()),
                        upper: Some(bound - U256::one()),
                        bottom: false,
                    }
                }
            }
            ConstraintOp::Le => Interval {
                lower: Some(U256::zero()),
                upper: Some(bound),
                bottom: false,
            },
            ConstraintOp::Gt => Interval {
                lower: Some(bound + U256::one()),
                upper: Some(max),
                bottom: false,
            },
            ConstraintOp::Ge => Interval {
                lower: Some(bound),
                upper: Some(max),
                bottom: false,
            },
            ConstraintOp::Eq => Interval {
                lower: Some(bound),
                upper: Some(bound),
                bottom: false,
            },
            ConstraintOp::Ne => return None,
        })
    }

    fn comparison_constraint(
        &self,
        lhs: &H::Exp,
        op: BinOp_,
        rhs: &H::Exp,
        truthy: bool,
        state: &AbstractState,
    ) -> Option<(H::Var, ConstraintOp, U256, String)> {
        let (var, bound, flip) = if let Some(var) = self.extract_var(lhs) {
            let bound = self.const_value(rhs, state)?;
            (var, bound, false)
        } else if let Some(var) = self.extract_var(rhs) {
            let bound = self.const_value(lhs, state)?;
            (var, bound, true)
        } else {
            return None;
        };
        let mut op = match op {
            BinOp_::Lt => ConstraintOp::Lt,
            BinOp_::Le => ConstraintOp::Le,
            BinOp_::Gt => ConstraintOp::Gt,
            BinOp_::Ge => ConstraintOp::Ge,
            BinOp_::Eq => ConstraintOp::Eq,
            BinOp_::Neq => ConstraintOp::Ne,
            _ => return None,
        };
        if flip {
            op = match op {
                ConstraintOp::Lt => ConstraintOp::Gt,
                ConstraintOp::Le => ConstraintOp::Ge,
                ConstraintOp::Gt => ConstraintOp::Lt,
                ConstraintOp::Ge => ConstraintOp::Le,
                other => other,
            };
        }
        if !truthy {
            op = match op {
                ConstraintOp::Lt => ConstraintOp::Ge,
                ConstraintOp::Le => ConstraintOp::Gt,
                ConstraintOp::Gt => ConstraintOp::Le,
                ConstraintOp::Ge => ConstraintOp::Lt,
                ConstraintOp::Eq => ConstraintOp::Ne,
                ConstraintOp::Ne => ConstraintOp::Eq,
            };
        }
        Some((var, op.clone(), bound, format!("{} {} {}", var.value(), op, bound)))
    }

    fn apply_constraint(
        &self,
        var: H::Var,
        op: ConstraintOp,
        bound: U256,
        text: String,
        state: &mut AbstractState,
    ) {
        let mut value = self.lookup_var(state, &var);
        value.interval = match op {
            ConstraintOp::Lt => {
                if bound == U256::zero() {
                    Interval::bottom()
                } else {
                    value.interval.intersect(None, Some(bound - U256::one()))
                }
            }
            ConstraintOp::Le => value.interval.intersect(None, Some(bound)),
            ConstraintOp::Gt => value.interval.intersect(Some(bound + U256::one()), None),
            ConstraintOp::Ge => value.interval.intersect(Some(bound), None),
            ConstraintOp::Eq => value.interval.intersect(Some(bound), Some(bound)),
            ConstraintOp::Ne => value.interval.clone(),
        };
        if value.interval.bottom {
            state.unreachable = true;
        } else {
            let strict_positive = value.interval.lower.is_some_and(|lower| lower > U256::zero());
            if let Some(facts) = &mut value.formula_facts {
                let var_name = var.value().to_string();
                for factor in &mut facts.factors {
                    if factor.name == var_name {
                        factor.strict_positive = strict_positive;
                    }
                }
            }
            state.locals.insert(var, value);
            let fact = PathFact {
                var: Some(var),
                op,
                bound: Some(bound),
                text,
            };
            if !state.path_facts.contains(&fact) {
                state.path_facts.push(fact);
            }
        }
    }

    fn eval_exp(&mut self, exp: &H::Exp, state: &AbstractState) -> Vec<ValueState> {
        use H::UnannotatedExp_ as E;
        match &exp.exp.value {
            E::Unit { .. } | E::Unreachable | E::UnresolvedError => vec![],
            E::Value(value) => vec![self.value_from_constant(value)],
            E::Move { var, .. } | E::Copy { var, .. } => vec![self.lookup_var(state, var)],
            E::Constant(_) => vec![type_interval(&exp.ty)],
            E::ErrorConstant { .. } => vec![ValueState::exact_uint(256, U256::zero())],
            E::Freeze(inner) | E::Dereference(inner) => self.eval_exp(inner, state),
            E::BorrowLocal(_, var) => vec![self.lookup_var(state, var)],
            E::Borrow(_, inner, _, _) => self.eval_exp(inner, state),
            E::UnaryExp(sp!(_, UnaryOp_::Not), inner) => {
                let _ = self.eval_exp(inner, state);
                vec![ValueState {
                    interval: Interval {
                        lower: Some(U256::zero()),
                        upper: Some(U256::one()),
                        bottom: false,
                    },
                    term: SymbolicTerm::Unknown,
                    bit_facts: None,
                    formula_facts: None,
                    parameter_dependencies: BTreeSet::new(),
                    risky_origins: vec![],
                }]
            }
            E::Multiple(values) => values
                .iter()
                .map(|value| self.eval_exp(value, state).into_iter().next().unwrap_or_else(ValueState::top))
                .collect(),
            E::Vector(_, _, _, values) => {
                for value in values {
                    let _ = self.eval_exp(value, state);
                }
                vec![type_interval(&exp.ty)]
            }
            E::Pack(_, _, fields) | E::PackVariant(_, _, _, fields) => {
                for (_, _, field_exp) in fields {
                    let _ = self.eval_exp(field_exp, state);
                }
                vec![type_interval(&exp.ty)]
            }
            E::ModuleCall(call) => self.eval_module_call(call, exp, state),
            E::Cast(inner, builtin) => {
                let mut value = self
                    .eval_exp(inner, state)
                    .into_iter()
                    .next()
                    .unwrap_or_else(ValueState::top);
                if let Some(dest_width) = builtin_width(&builtin.value) {
                    let max_value = cast_max(dest_width);
                    if value.interval.upper.is_some_and(|upper| upper <= max_value) {
                        value.interval = value.interval.intersect(Some(U256::zero()), Some(max_value));
                    } else {
                        let source_name = self.describe_exp(inner);
                        let origin = RiskOrigin {
                            key: format!(
                                "{}:{}:{}",
                                RiskKind::ReachableNarrowCast.rule_id(),
                                exp.exp.loc.file_hash(),
                                exp.exp.loc.start()
                            ),
                            kind: RiskKind::ReachableNarrowCast,
                            loc: exp.exp.loc,
                            source_param_index: self.single_parameter_dependency(&value),
                            width: Some(dest_width),
                            shift_amount: None,
                            threshold: Some(max_value),
                            title: "Reachable narrowing cast on value-bearing path".to_string(),
                            expr_text: self.describe_exp(exp),
                            failed_condition: format!("{source_name} <= {max_value}"),
                            path_facts: self.path_fact_texts(state),
                            source_interval: value.interval.describe(),
                            source_name,
                            helper_name: Some(self.info.key.name.to_string()),
                            helper_like: looks_like_helper(&self.info.key.name.to_string()),
                            guard_mismatch: false,
                        };
                        self.push_origin(&mut value, origin);
                        value.interval = value.interval.intersect(Some(U256::zero()), Some(max_value));
                    }
                    value.bit_facts = Some(
                        value
                            .bit_facts
                            .unwrap_or_else(|| BitFacts::unknown(dest_width))
                    );
                    if let Some(facts) = &mut value.bit_facts {
                        facts.width = dest_width;
                        let mask = width_mask(dest_width);
                        facts.known_zero = facts.known_zero | (U256::max_value() ^ mask);
                        facts.known_one &= mask;
                    }
                    value.refine_with_bit_facts();
                }
                value.risky_origins
                    .retain(|origin| origin.kind != RiskKind::SuspiciousBitwiseArithmetic);
                self.emit_arithmetic_use(
                    &value.risky_origins,
                    exp.exp.loc,
                    state,
                    Some(self.describe_exp(exp)),
                    true,
                );
                vec![value]
            }
            E::BinopExp(lhs, op, rhs) => {
                let left = self
                    .eval_exp(lhs, state)
                    .into_iter()
                    .next()
                    .unwrap_or_else(ValueState::top);
                let right = self
                    .eval_exp(rhs, state)
                    .into_iter()
                    .next()
                    .unwrap_or_else(ValueState::top);
                vec![self.eval_binop(exp, lhs, left, op.value, rhs, right, state)]
            }
        }
    }

    fn eval_module_call(
        &mut self,
        call: &H::ModuleCall,
        exp: &H::Exp,
        state: &AbstractState,
    ) -> Vec<ValueState> {
        let argument_values: Vec<ValueState> = call
            .arguments
            .iter()
            .map(|argument| {
                self.eval_exp(argument, state)
                    .into_iter()
                    .next()
                    .unwrap_or_else(ValueState::top)
            })
            .collect();

        let call_name = call.name.to_string();
        if looks_like_sink_call(&call_name) {
            let financial = looks_like_financial_name(&call_name);
            for argument in &argument_values {
                for origin in &argument.risky_origins {
                    self.emit_sink(origin, exp.exp.loc, SinkKind::CallArgument, financial, state, Some(call_name.clone()));
                }
            }
        }

        let default_returns = type_components(&exp.ty)
            .into_iter()
            .map(|component| type_interval(&component))
            .collect::<Vec<_>>();
        let callee_key = FunctionKey {
            module: call.module,
            name: call.name,
        };
        let Some(summary) = self.summaries.get(&callee_key) else {
            return if default_returns.is_empty() {
                vec![type_interval(&exp.ty)]
            } else {
                default_returns
            };
        };
        if summary.returns.is_empty() {
            return default_returns;
        }
        let mut results = vec![];
        for (index, return_summary) in summary.returns.iter().enumerate() {
            let mut value = default_returns.get(index).cloned().unwrap_or_else(ValueState::top);
            let mut dependencies = BTreeSet::new();
            for dependency in &return_summary.parameter_dependencies {
                if let Some(argument) = argument_values.get(*dependency) {
                    dependencies.extend(argument.parameter_dependencies.iter().copied());
                    for origin in &argument.risky_origins {
                        if value.risky_origins.iter().all(|existing| existing.key != origin.key) {
                            value.risky_origins.push(origin.clone());
                        }
                    }
                }
            }
            value.parameter_dependencies = dependencies;

            for origin in &return_summary.risky_origins {
                if let Some(param_index) = origin.source_param_index
                    && let Some(argument) = argument_values.get(param_index)
                    && let Some(threshold) = origin.threshold
                    && argument.interval.upper.is_some_and(|upper| upper <= threshold)
                {
                    continue;
                }
                let mut mapped_origin = origin.clone();
                mapped_origin.source_param_index = origin
                    .source_param_index
                    .and_then(|param_index| argument_values.get(param_index))
                    .and_then(|argument| self.single_parameter_dependency(argument));
                if value
                    .risky_origins
                    .iter()
                    .all(|existing| existing.key != mapped_origin.key)
                {
                    value.risky_origins.push(mapped_origin);
                }
            }
            if call_name.contains("mul") && argument_values.len() >= 2 {
                value.formula_facts =
                    self.combine_mul_formula(&argument_values[0], &argument_values[1]);
            }
            if call_name.contains("div") && argument_values.len() >= 2 {
                if let Some(origin) = self.make_weak_denominator_origin(
                    exp,
                    &argument_values[0],
                    &call.arguments[0],
                    &argument_values[1],
                    &call.arguments[1],
                    state,
                ) {
                    self.push_origin(&mut value, origin);
                }
            }
            results.push(value);
        }
        results
    }

    fn eval_binop(
        &mut self,
        exp: &H::Exp,
        lhs_exp: &H::Exp,
        lhs: ValueState,
        op: BinOp_,
        _rhs_exp: &H::Exp,
        rhs: ValueState,
        state: &AbstractState,
    ) -> ValueState {
        let mut value = lhs.join(&rhs);
        value.term = SymbolicTerm::Opaque(self.describe_exp(exp));
        let result_builtin = type_builtin(&exp.ty);
        let result_width = result_builtin.and_then(|builtin| builtin_width(&builtin));
        let result_max = result_width.map(uint_max);

        match op {
            BinOp_::Add => {
                value.interval = checked_binary_interval(&lhs.interval, &rhs.interval, result_width, U256::checked_add);
                value.bit_facts = self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| l.checked_add(r));
                value.formula_facts = None;
            }
            BinOp_::Sub => {
                value.interval = checked_binary_interval(&lhs.interval, &rhs.interval, result_width, U256::checked_sub);
                value.bit_facts = self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| l.checked_sub(r));
                value.formula_facts = self.combine_sub_formula(&lhs, &rhs);
            }
            BinOp_::Mul => {
                value.interval = checked_binary_interval(&lhs.interval, &rhs.interval, result_width, U256::checked_mul);
                value.bit_facts = self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| l.checked_mul(r));
                value.formula_facts = self.combine_mul_formula(&lhs, &rhs);
            }
            BinOp_::Div => {
                if rhs.interval.lower.is_some_and(|lower| lower > U256::zero())
                    && let (Some(lo), Some(hi), Some(rlo), Some(rhi)) =
                        (lhs.interval.lower, lhs.interval.upper, rhs.interval.lower, rhs.interval.upper)
                {
                    value.interval = Interval {
                        lower: Some(lo / rhi),
                        upper: Some(hi / rlo),
                        bottom: false,
                    };
                } else {
                    value.interval = result_width.map_or_else(Interval::top, |width| {
                        Interval {
                            lower: Some(U256::zero()),
                            upper: Some(uint_max(width)),
                            bottom: false,
                        }
                    });
                }
                value.bit_facts = self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| {
                    if r == U256::zero() {
                        None
                    } else {
                        l.checked_div(r)
                    }
                });
                value.formula_facts = None;
                if let Some(origin) =
                    self.make_weak_denominator_origin(exp, &lhs, lhs_exp, &rhs, _rhs_exp, state)
                {
                    self.push_origin(&mut value, origin);
                }
            }
            BinOp_::Mod => {
                value.interval = result_width.map_or_else(Interval::top, |width| {
                    Interval {
                        lower: Some(U256::zero()),
                        upper: Some(uint_max(width)),
                        bottom: false,
                    }
                });
                value.bit_facts = self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| {
                    if r == U256::zero() {
                        None
                    } else {
                        l.checked_rem(r)
                    }
                });
                value.formula_facts = None;
            }
            BinOp_::BitAnd => {
                if let Some(width) = result_width {
                    let facts = self.bit_facts_for_binary(width, &lhs, &rhs, BitwiseOp::And);
                    value.bit_facts = Some(facts);
                    value.interval = Interval {
                        lower: Some(U256::zero()),
                        upper: Some(width_mask(width)),
                        bottom: false,
                    };
                    value.refine_with_bit_facts();
                    if value.exact_value().is_none() {
                        self.push_origin(
                            &mut value,
                            self.make_origin(
                                RiskKind::SuspiciousBitwiseArithmetic,
                                exp,
                                &lhs,
                                lhs_exp,
                                state,
                                Some(width),
                                None,
                                None,
                                "Bitwise arithmetic result remains non-exact before downstream use".to_string(),
                                "Suspicious bitwise result may influence downstream arithmetic".to_string(),
                                false,
                            ),
                        );
                    }
                }
                value.formula_facts = None;
            }
            BinOp_::BitOr => {
                if let Some(width) = result_width {
                    let facts = self.bit_facts_for_binary(width, &lhs, &rhs, BitwiseOp::Or);
                    value.bit_facts = Some(facts);
                    value.interval = Interval {
                        lower: Some(U256::zero()),
                        upper: Some(width_mask(width)),
                        bottom: false,
                    };
                    value.refine_with_bit_facts();
                    if value.exact_value().is_none() {
                        self.push_origin(
                            &mut value,
                            self.make_origin(
                                RiskKind::SuspiciousBitwiseArithmetic,
                                exp,
                                &lhs,
                                lhs_exp,
                                state,
                                Some(width),
                                None,
                                None,
                                "Bitwise arithmetic result remains non-exact before downstream use".to_string(),
                                "Suspicious bitwise result may influence downstream arithmetic".to_string(),
                                false,
                            ),
                        );
                    }
                }
                value.formula_facts = None;
            }
            BinOp_::Xor => {
                if let Some(width) = result_width {
                    let facts = self.bit_facts_for_binary(width, &lhs, &rhs, BitwiseOp::Xor);
                    value.bit_facts = Some(facts);
                    value.interval = Interval {
                        lower: Some(U256::zero()),
                        upper: Some(width_mask(width)),
                        bottom: false,
                    };
                    value.refine_with_bit_facts();
                    if value.exact_value().is_none() {
                        self.push_origin(
                            &mut value,
                            self.make_origin(
                                RiskKind::SuspiciousBitwiseArithmetic,
                                exp,
                                &lhs,
                                lhs_exp,
                                state,
                                Some(width),
                                None,
                                None,
                                "Bitwise arithmetic result remains non-exact before downstream use".to_string(),
                                "Suspicious bitwise result may influence downstream arithmetic".to_string(),
                                false,
                            ),
                        );
                    }
                }
                value.formula_facts = None;
            }
            BinOp_::Shl => {
                if let Some(width) = result_width {
                    let shift_amount = rhs.exact_value().map(|value| value.unchecked_as_u8());
                    if let Some(shift_amount) = shift_amount {
                        if (shift_amount as u16) >= width {
                            self.push_origin(
                                &mut value,
                                self.make_origin(
                                    RiskKind::InvalidShiftCount,
                                    exp,
                                    &rhs,
                                    _rhs_exp,
                                    state,
                                    Some(width),
                                    Some(shift_amount),
                                    None,
                                    format!("{shift_amount} < {width}"),
                                    "Invalid shift count is reachable".to_string(),
                                    false,
                                ),
                            );
                            value.interval = Interval::top();
                            value.bit_facts = Some(BitFacts::unknown(width));
                        } else {
                            let threshold = no_truncation_threshold(width, shift_amount);
                            let guard_upper_bound = self.strongest_upper_bound(lhs_exp, state);
                            let helper_like = looks_like_helper(&self.info.key.name.to_string());
                            if lhs.interval.upper.is_some_and(|upper| upper <= threshold) {
                                if let (Some(lo), Some(hi)) = (lhs.interval.lower, lhs.interval.upper) {
                                    value.interval = Interval {
                                        lower: lo.checked_shl(shift_amount as u32),
                                        upper: hi.checked_shl(shift_amount as u32),
                                        bottom: false,
                                    };
                                }
                                value.bit_facts = lhs.bit_facts.as_ref().map(|facts| facts.shift_left(shift_amount, width));
                                value.refine_with_bit_facts();
                            } else {
                                let kind = if helper_like
                                    && guard_is_weaker_than_threshold(guard_upper_bound, threshold)
                                {
                                    RiskKind::FakeCheckedShift
                                } else {
                                    RiskKind::ReachableShiftTruncation
                                };
                                self.push_origin(
                                    &mut value,
                                    self.make_origin(
                                        kind,
                                        exp,
                                        &lhs,
                                        lhs_exp,
                                        state,
                                        Some(width),
                                        Some(shift_amount),
                                        Some(threshold),
                                        format!(
                                            "{} <= {threshold} (MAX_U{width} >> {shift_amount})",
                                            self.describe_exp(lhs_exp)
                                        ),
                                        if helper_like {
                                            "Unsound checked-shift helper is reachable".to_string()
                                        } else {
                                            "Reachable truncating left shift".to_string()
                                        },
                                        guard_is_weaker_than_threshold(guard_upper_bound, threshold),
                                    ),
                                );
                                value.interval = Interval {
                                    lower: Some(U256::zero()),
                                    upper: result_max,
                                    bottom: false,
                                };
                                value.bit_facts = Some(BitFacts::unknown(width));
                            }
                        }
                    } else if width == 256 {
                        self.push_origin(
                            &mut value,
                            self.make_origin(
                                RiskKind::DynamicU256Shift,
                                exp,
                                &rhs,
                                _rhs_exp,
                                state,
                                Some(width),
                                None,
                                None,
                                "shift amount is a reachable non-constant u256 driver".to_string(),
                                "Dynamic u256 shift count is reachable".to_string(),
                                false,
                            ),
                        );
                        value.interval = Interval {
                            lower: Some(U256::zero()),
                            upper: result_max,
                            bottom: false,
                        };
                        value.bit_facts = Some(BitFacts::unknown(width));
                    } else {
                        value.interval = Interval {
                            lower: Some(U256::zero()),
                            upper: result_max,
                            bottom: false,
                        };
                        value.bit_facts = Some(BitFacts::unknown(width));
                    }
                }
                value.formula_facts = None;
            }
            BinOp_::Shr => {
                if let Some(width) = result_width {
                    let shift_amount = rhs.exact_value().map(|value| value.unchecked_as_u8());
                    if let Some(shift_amount) = shift_amount {
                        if (shift_amount as u16) >= width {
                            self.push_origin(
                                &mut value,
                                self.make_origin(
                                    RiskKind::InvalidShiftCount,
                                    exp,
                                    &rhs,
                                    _rhs_exp,
                                    state,
                                    Some(width),
                                    Some(shift_amount),
                                    None,
                                    format!("{shift_amount} < {width}"),
                                    "Invalid shift count is reachable".to_string(),
                                    false,
                                ),
                            );
                            value.interval = Interval::top();
                            value.bit_facts = Some(BitFacts::unknown(width));
                        } else {
                            if let (Some(lo), Some(hi)) = (lhs.interval.lower, lhs.interval.upper) {
                                value.interval = Interval {
                                    lower: lo.checked_shr(shift_amount as u32),
                                    upper: hi.checked_shr(shift_amount as u32),
                                    bottom: false,
                                };
                            }
                            value.bit_facts = lhs.bit_facts.as_ref().map(|facts| facts.shift_right(shift_amount, width));
                            value.refine_with_bit_facts();
                            let discarded_mask = low_mask(shift_amount) & width_mask(width);
                            if discarded_mask != U256::zero() && lhs.may_have_non_zero_bits(discarded_mask) {
                                self.push_origin(
                                    &mut value,
                                    self.make_origin(
                                        RiskKind::ReachableLossyRightShift,
                                        exp,
                                        &lhs,
                                        lhs_exp,
                                        state,
                                        Some(width),
                                        Some(shift_amount),
                                        None,
                                        format!("({} & {}) == 0", self.describe_exp(lhs_exp), discarded_mask),
                                        "Right shift may discard non-zero low bits".to_string(),
                                        false,
                                    ),
                                );
                            }
                        }
                    } else if width == 256 {
                        self.push_origin(
                            &mut value,
                            self.make_origin(
                                RiskKind::DynamicU256Shift,
                                exp,
                                &rhs,
                                _rhs_exp,
                                state,
                                Some(width),
                                None,
                                None,
                                "shift amount is a reachable non-constant u256 driver".to_string(),
                                "Dynamic u256 shift count is reachable".to_string(),
                                false,
                            ),
                        );
                        value.interval = Interval {
                            lower: Some(U256::zero()),
                            upper: result_max,
                            bottom: false,
                        };
                        value.bit_facts = Some(BitFacts::unknown(width));
                    } else {
                        value.interval = Interval {
                            lower: Some(U256::zero()),
                            upper: result_max,
                            bottom: false,
                        };
                        value.bit_facts = Some(BitFacts::unknown(width));
                    }
                }
                value.formula_facts = None;
            }
            BinOp_::Eq | BinOp_::Neq | BinOp_::Lt | BinOp_::Le | BinOp_::Gt | BinOp_::Ge | BinOp_::And | BinOp_::Or => {
                value.interval = Interval {
                    lower: Some(U256::zero()),
                    upper: Some(U256::one()),
                    bottom: false,
                };
                value.bit_facts = None;
                value.formula_facts = None;
            }
            _ => {
                value.interval = Interval::top();
                value.bit_facts = None;
                value.formula_facts = None;
            }
        }
        let has_shift_or_precision_origin = value.risky_origins.iter().any(|origin| {
            matches!(
                origin.kind,
                RiskKind::ReachableShiftTruncation
                    | RiskKind::FakeCheckedShift
                    | RiskKind::InvalidShiftCount
                    | RiskKind::ReachableLossyRightShift
                    | RiskKind::DynamicU256Shift
            )
        });
        let suppress_suspicious = has_shift_or_precision_origin || matches!(op, BinOp_::Shl | BinOp_::Shr);
        if suppress_suspicious {
            value.risky_origins
                .retain(|origin| origin.kind != RiskKind::SuspiciousBitwiseArithmetic);
        }
        if matches!(
            op,
            BinOp_::Add
                | BinOp_::Sub
                | BinOp_::Mul
                | BinOp_::Div
                | BinOp_::Mod
                | BinOp_::Shl
                | BinOp_::Shr
        ) {
            let detail = Some(self.describe_exp(exp));
            self.emit_arithmetic_use(&lhs.risky_origins, exp.exp.loc, state, detail.clone(), suppress_suspicious);
            self.emit_arithmetic_use(&rhs.risky_origins, exp.exp.loc, state, detail, suppress_suspicious);
        }
        value
    }

    fn derive_numeric_bit_facts(
        &self,
        lhs: &ValueState,
        rhs: &ValueState,
        width: Option<u16>,
        op: impl Fn(U256, U256) -> Option<U256>,
    ) -> Option<BitFacts> {
        let width = width?;
        let lhs = lhs.exact_value()?;
        let rhs = rhs.exact_value()?;
        Some(BitFacts::exact(width, op(lhs, rhs)?))
    }

    fn combine_sub_formula(&self, lhs: &ValueState, rhs: &ValueState) -> Option<FormulaFacts> {
        let lhs_facts = lhs.formula_facts.as_ref()?;
        let rhs_facts = rhs.formula_facts.as_ref()?;
        if lhs_facts.tags.contains(&FormulaTag::PriceLike)
            && rhs_facts.tags.contains(&FormulaTag::PriceLike)
        {
            let mut tags = formula_tags_from_name("sqrt_price_diff");
            tags.insert(FormulaTag::PriceDiff);
            Some(FormulaFacts { tags, factors: vec![] })
        } else {
            None
        }
    }

    fn combine_mul_formula(&self, lhs: &ValueState, rhs: &ValueState) -> Option<FormulaFacts> {
        let mut tags = BTreeSet::new();
        let mut factors = vec![];
        if let Some(lhs_facts) = &lhs.formula_facts {
            tags.extend(lhs_facts.tags.iter().cloned());
            factors.extend(lhs_facts.factors.iter().cloned());
        }
        if let Some(rhs_facts) = &rhs.formula_facts {
            tags.extend(rhs_facts.tags.iter().cloned());
            factors.extend(rhs_facts.factors.iter().cloned());
        }
        if factors.is_empty() {
            return None;
        }
        let lhs_tags = lhs
            .formula_facts
            .as_ref()
            .map(|facts| &facts.tags)
            .cloned()
            .unwrap_or_default();
        let rhs_tags = rhs
            .formula_facts
            .as_ref()
            .map(|facts| &facts.tags)
            .cloned()
            .unwrap_or_default();
        if lhs_tags.contains(&FormulaTag::PriceLike) && rhs_tags.contains(&FormulaTag::PriceLike) {
            tags.insert(FormulaTag::PriceProduct);
            tags.insert(FormulaTag::ClmmDenominator);
            tags.insert(FormulaTag::DenominatorLike);
        }
        if (lhs_tags.contains(&FormulaTag::LiquidityLike) && rhs_tags.contains(&FormulaTag::PriceDiff))
            || (rhs_tags.contains(&FormulaTag::LiquidityLike)
                && lhs_tags.contains(&FormulaTag::PriceDiff))
        {
            tags.insert(FormulaTag::LiquidityScaled);
            tags.insert(FormulaTag::ClmmNumerator);
        }
        Some(FormulaFacts { tags, factors })
    }

    fn make_weak_denominator_origin(
        &self,
        exp: &H::Exp,
        numerator: &ValueState,
        numerator_exp: &H::Exp,
        denominator: &ValueState,
        denominator_exp: &H::Exp,
        state: &AbstractState,
    ) -> Option<RiskOrigin> {
        let denom_facts = denominator.formula_facts.as_ref()?;
        let price_like_factors = denom_facts
            .factors
            .iter()
            .filter(|factor| factor.tags.contains(&FormulaTag::PriceLike))
            .collect::<Vec<_>>();
        let price_like_factor_count = price_like_factors.len();
        let structural_denominator = denom_facts.tags.contains(&FormulaTag::ClmmDenominator)
            || price_like_factor_count >= 2;
        if !structural_denominator {
            return None;
        }
        let is_clmm_like = denom_facts.tags.contains(&FormulaTag::ClmmDenominator)
            && numerator
                .formula_facts
                .as_ref()
                .is_some_and(|facts| facts.tags.contains(&FormulaTag::ClmmNumerator));
        let relevant_factors = if price_like_factor_count >= 2 {
            price_like_factors
        } else {
            denom_facts.factors.iter().collect::<Vec<_>>()
        };
        let all_relevant_factors_strict_positive =
            !relevant_factors.is_empty() && relevant_factors.iter().all(|factor| factor.strict_positive);
        let zero_reachable = if all_relevant_factors_strict_positive {
            false
        } else {
            denominator
                .interval
                .lower
                .is_none_or(|lower| lower == U256::zero())
        };
        if !zero_reachable && all_relevant_factors_strict_positive {
            return None;
        }
        if !zero_reachable && !is_clmm_like {
            return None;
        }
        let factor_condition = if relevant_factors.is_empty() {
            format!("{} > 0", self.describe_exp(denominator_exp))
        } else {
            relevant_factors
                .iter()
                .map(|factor| format!("{} > 0", factor.name))
                .collect::<Vec<_>>()
                .join(" && ")
        };
        let title = if zero_reachable {
            if is_clmm_like {
                "CLMM denominator may be zero on a reachable quote path"
            } else {
                "Denominator may be zero on a reachable value-bearing path"
            }
        } else if is_clmm_like {
            "CLMM denominator factors are not independently proven positive"
        } else {
            "Denominator factors are not independently proven positive"
        }
        .to_string();
        let source_value = if zero_reachable { denominator } else { numerator };
        let source_exp = if zero_reachable {
            denominator_exp
        } else {
            numerator_exp
        };
        Some(RiskOrigin {
            key: format!(
                "{}:{}:{}",
                RiskKind::ReachableWeakDenominator.rule_id(),
                exp.exp.loc.file_hash(),
                exp.exp.loc.start()
            ),
            kind: RiskKind::ReachableWeakDenominator,
            loc: exp.exp.loc,
            source_param_index: self.single_parameter_dependency(denominator),
            width: denominator.width(),
            shift_amount: None,
            threshold: if zero_reachable {
                Some(U256::zero())
            } else {
                None
            },
            title,
            expr_text: self.describe_exp(exp),
            failed_condition: factor_condition,
            path_facts: self.path_fact_texts(state),
            source_interval: source_value.interval.describe(),
            source_name: self.describe_exp(source_exp),
            helper_name: Some(self.info.key.name.to_string()),
            helper_like: looks_like_helper(&self.info.key.name.to_string()),
            guard_mismatch: false,
        })
    }

    fn bit_facts_for_binary(
        &self,
        width: u16,
        lhs: &ValueState,
        rhs: &ValueState,
        op: BitwiseOp,
    ) -> BitFacts {
        let lhs_facts = lhs
            .bit_facts
            .clone()
            .unwrap_or_else(|| BitFacts::unknown(width));
        let rhs_facts = rhs
            .bit_facts
            .clone()
            .unwrap_or_else(|| BitFacts::unknown(width));
        match op {
            BitwiseOp::And => lhs_facts.bitand(&rhs_facts, width),
            BitwiseOp::Or => lhs_facts.bitor(&rhs_facts, width),
            BitwiseOp::Xor => lhs_facts.bitxor(&rhs_facts, width),
        }
    }

    fn make_origin(
        &self,
        kind: RiskKind,
        exp: &H::Exp,
        source_value: &ValueState,
        source_exp: &H::Exp,
        state: &AbstractState,
        width: Option<u16>,
        shift_amount: Option<u8>,
        threshold: Option<U256>,
        failed_condition: String,
        title: String,
        guard_mismatch: bool,
    ) -> RiskOrigin {
        RiskOrigin {
            key: format!(
                "{}:{}:{}",
                kind.rule_id(),
                exp.exp.loc.file_hash(),
                exp.exp.loc.start()
            ),
            kind,
            loc: exp.exp.loc,
            source_param_index: self.single_parameter_dependency(source_value),
            width,
            shift_amount,
            threshold,
            title,
            expr_text: self.describe_exp(exp),
            failed_condition,
            path_facts: self.path_fact_texts(state),
            source_interval: source_value.interval.describe(),
            source_name: self.describe_exp(source_exp),
            helper_name: Some(self.info.key.name.to_string()),
            helper_like: looks_like_helper(&self.info.key.name.to_string()),
            guard_mismatch,
        }
    }

    fn push_origin(&self, value: &mut ValueState, origin: RiskOrigin) {
        if value
            .risky_origins
            .iter()
            .all(|existing| existing.key != origin.key)
        {
            value.risky_origins.push(origin);
        }
    }

    fn emit_arithmetic_use(
        &mut self,
        origins: &[RiskOrigin],
        sink_loc: Loc,
        state: &AbstractState,
        detail: Option<String>,
        suppress_suspicious: bool,
    ) {
        for origin in origins {
            if !matches!(
                origin.kind,
                RiskKind::ReachableLossyRightShift
                    | RiskKind::DynamicU256Shift
                    | RiskKind::SuspiciousBitwiseArithmetic
                    | RiskKind::ReachableWeakDenominator
            ) {
                continue;
            }
            if suppress_suspicious && origin.kind == RiskKind::SuspiciousBitwiseArithmetic {
                continue;
            }
            self.emit_sink(
                origin,
                sink_loc,
                SinkKind::ArithmeticUse,
                false,
                state,
                detail.clone(),
            );
        }
    }

    fn emit_sink(
        &mut self,
        origin: &RiskOrigin,
        sink_loc: Loc,
        sink_kind: SinkKind,
        financial: bool,
        state: &AbstractState,
        detail: Option<String>,
    ) {
        if self.mode != AnalysisMode::Findings {
            return;
        }
        let priority = sink_priority(&sink_kind, financial);
        let severity = match origin.kind {
            RiskKind::DynamicU256Shift | RiskKind::SuspiciousBitwiseArithmetic => {
                Severity::Warning
            }
            RiskKind::ReachableLossyRightShift => {
                if priority >= 3 {
                    Severity::NonblockingError
                } else {
                    Severity::Warning
                }
            }
            RiskKind::ReachableWeakDenominator => {
                if origin.threshold == Some(U256::zero()) && priority >= 1 {
                    Severity::NonblockingError
                } else {
                    Severity::Warning
                }
            }
            _ => {
                if priority >= 3 {
                    Severity::NonblockingError
                } else {
                    Severity::Warning
                }
            }
        };
        let title = match origin.kind {
            RiskKind::ReachableShiftTruncation => "Reachable truncating left shift on a value-bearing path",
            RiskKind::FakeCheckedShift => "Custom checked-shift helper may be unsound on a reachable path",
            RiskKind::ReachableNarrowCast => "Reachable narrowing cast may fail on a value-bearing path",
            RiskKind::InvalidShiftCount => "Reachable invalid shift count",
            RiskKind::ReachableLossyRightShift => "Reachable lossy right shift on a value-bearing path",
            RiskKind::DynamicU256Shift => "Dynamic u256 shift count reaches value-sensitive logic",
            RiskKind::SuspiciousBitwiseArithmetic => "Suspicious bitwise result reaches downstream arithmetic",
            RiskKind::ReachableWeakDenominator => origin.title.as_str(),
        }
        .to_string();
        let mut path_facts = origin.path_facts.clone();
        for fact in self.path_fact_texts(state) {
            if !path_facts.contains(&fact) {
                path_facts.push(fact);
            }
        }
        let mut message = format!(
            "{}. The analyzer cannot prove `{}`. Current path facts: {}. Source interval: {}.",
            origin.expr_text,
            origin.failed_condition,
            if path_facts.is_empty() {
                "none".to_string()
            } else {
                path_facts.join(", ")
            },
            origin.source_interval
        );
        if origin.guard_mismatch {
            message.push_str(" A dominating helper guard exists, but it is weaker than the true no-truncation bound.");
        }
        if origin.kind == RiskKind::DynamicU256Shift {
            message.push_str(" Unlike u8-u128 shifts, u256 shift counts are not runtime-checked by the Move VM.");
        }
        if let Some(ref detail) = detail {
            message.push_str(&format!(" Sink evidence: {detail}."));
        }
        let recommendation = match origin.kind {
            RiskKind::ReachableShiftTruncation | RiskKind::FakeCheckedShift => {
                "Enforce the canonical bound before shifting, or widen the intermediate and only narrow after an exact bound check.".to_string()
            }
            RiskKind::ReachableNarrowCast => {
                "Prove the destination range before casting, or keep the value in the wider type through value-sensitive math.".to_string()
            }
            RiskKind::InvalidShiftCount => {
                "Prove the shift amount is strictly smaller than the operand width on every reachable path.".to_string()
            }
            RiskKind::ReachableLossyRightShift => {
                "Prove the discarded low bits are zero before using right shift as arithmetic, or use an exact division path where rounding is explicit.".to_string()
            }
            RiskKind::DynamicU256Shift => {
                "Use a constant shift amount or prove and guard the u256 shift count explicitly before value-sensitive math.".to_string()
            }
            RiskKind::SuspiciousBitwiseArithmetic => {
                "Prove the masked or combined bit range before reusing the value in arithmetic or sink-bearing logic.".to_string()
            }
            RiskKind::ReachableWeakDenominator => {
                "Prove every denominator factor is strictly positive before dividing, and add explicit CLMM price-bound guards instead of relying on opaque helper behavior.".to_string()
            }
        };
        self.current_outcome.findings.push(SecurityFinding {
            key: origin.key.clone(),
            kind: origin.kind.clone(),
            loc: origin.loc,
            sink_loc: Some(sink_loc),
            helper_loc: origin.helper_name.as_ref().map(|_| origin.loc),
            severity,
            title,
            message,
            failed_condition: origin.failed_condition.clone(),
            path_facts,
            recommendation,
            sink_kind,
            sink_detail: detail,
        });
    }

    fn assign_lvalue(&self, lvalue: &H::LValue, value: ValueState, state: &mut AbstractState) {
        match &lvalue.value {
            H::LValue_::Var { var, .. } => {
                let mut value = value;
                self.annotate_value_with_name(&mut value, &var.value().to_string());
                state.locals.insert(*var, value);
            }
            H::LValue_::Ignore
            | H::LValue_::Unpack(_, _, _)
            | H::LValue_::UnpackVariant(_, _, _, _, _, _) => {}
        }
    }

    fn lookup_var(&self, state: &AbstractState, var: &H::Var) -> ValueState {
        state
            .locals
            .get(var)
            .cloned()
            .unwrap_or_else(|| {
                self.local_types
                    .get(var)
                    .map(type_interval)
                    .unwrap_or_else(ValueState::top)
            })
    }

    fn annotate_value_with_name(&self, value: &mut ValueState, name: &str) {
        let strict_positive = value.interval.lower.is_some_and(|lower| lower > U256::zero());
        let tags = formula_tags_from_name(name);
        if tags.is_empty() {
            return;
        }
        match &mut value.formula_facts {
            Some(facts) => {
                facts.merge_tags(tags.clone());
                if let Some(existing) = facts.factors.iter_mut().find(|factor| factor.name == name) {
                    existing.strict_positive = strict_positive;
                    existing.tags.extend(tags);
                } else {
                    facts.factors.push(crate::security_analysis::domain::FormulaFactor::new(
                        name.to_string(),
                        tags,
                        strict_positive,
                    ));
                }
            }
            None => {
                value.formula_facts = FormulaFacts::from_name(name, strict_positive);
            }
        }
    }

    fn value_from_constant(&self, value: &H::Value) -> ValueState {
        if let Some(integer) = integer_value(value) {
            let width = match value.value {
                H::Value_::U8(_) => 8,
                H::Value_::U16(_) => 16,
                H::Value_::U32(_) => 32,
                H::Value_::U64(_) => 64,
                H::Value_::U128(_) => 128,
                H::Value_::U256(_) => 256,
                _ => 256,
            };
            ValueState::exact_uint(width, integer)
        } else if let H::Value_::Bool(_) = value.value {
            ValueState {
                interval: Interval {
                    lower: Some(U256::zero()),
                    upper: Some(U256::one()),
                    bottom: false,
                },
                term: SymbolicTerm::Unknown,
                bit_facts: None,
                formula_facts: None,
                parameter_dependencies: BTreeSet::new(),
                risky_origins: vec![],
            }
        } else {
            ValueState::top()
        }
    }

    fn is_publicish(&self) -> bool {
        !matches!(self.info.function.visibility, H::Visibility::Internal) || self.info.function.entry.is_some()
    }

    fn single_parameter_dependency(&self, value: &ValueState) -> Option<usize> {
        if value.parameter_dependencies.len() == 1 {
            value.parameter_dependencies.iter().next().copied()
        } else {
            None
        }
    }

    fn strongest_upper_bound(&self, exp: &H::Exp, state: &AbstractState) -> Option<U256> {
        let var = self.extract_var(exp)?;
        state
            .path_facts
            .iter()
            .filter(|fact| fact.var == Some(var))
            .filter_map(|fact| match fact.op {
                ConstraintOp::Lt => fact.bound.map(|bound| {
                    if bound == U256::zero() {
                        U256::zero()
                    } else {
                        bound - U256::one()
                    }
                }),
                ConstraintOp::Le | ConstraintOp::Eq => fact.bound,
                _ => None,
            })
            .min()
    }

    fn extract_var(&self, exp: &H::Exp) -> Option<H::Var> {
        match &exp.exp.value {
            H::UnannotatedExp_::Move { var, .. }
            | H::UnannotatedExp_::Copy { var, .. }
            | H::UnannotatedExp_::BorrowLocal(_, var) => Some(*var),
            H::UnannotatedExp_::Cast(inner, _) => self.extract_var(inner),
            _ => None,
        }
    }

    fn const_value(&self, exp: &H::Exp, state: &AbstractState) -> Option<U256> {
        use H::UnannotatedExp_ as E;
        match &exp.exp.value {
            E::Value(value) => integer_value(value),
            E::Move { var, .. } | E::Copy { var, .. } | E::BorrowLocal(_, var) => {
                self.lookup_var(state, var).exact_value()
            }
            E::Cast(inner, _) => self.const_value(inner, state),
            E::BinopExp(lhs, op, rhs) => {
                let lhs = self.const_value(lhs, state)?;
                let rhs = self.const_value(rhs, state)?;
                match op.value {
                    BinOp_::Add => lhs.checked_add(rhs),
                    BinOp_::Sub => lhs.checked_sub(rhs),
                    BinOp_::Mul => lhs.checked_mul(rhs),
                    BinOp_::Div => lhs.checked_div(rhs),
                    BinOp_::Mod => lhs.checked_rem(rhs),
                    BinOp_::BitAnd => Some(lhs & rhs),
                    BinOp_::BitOr => Some(lhs | rhs),
                    BinOp_::Xor => Some(lhs ^ rhs),
                    BinOp_::Shl => lhs.checked_shl(rhs.unchecked_as_u8() as u32),
                    BinOp_::Shr => lhs.checked_shr(rhs.unchecked_as_u8() as u32),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn path_fact_texts(&self, state: &AbstractState) -> Vec<String> {
        state.path_facts.iter().map(|fact| fact.text.clone()).collect()
    }

    fn describe_exp(&self, exp: &H::Exp) -> String {
        use H::UnannotatedExp_ as E;
        match &exp.exp.value {
            E::Value(value) => describe_value(value),
            E::Move { var, .. } | E::Copy { var, .. } => var.value().to_string(),
            E::Constant(name) => name.to_string(),
            E::ErrorConstant { .. } => "error_constant".to_string(),
            E::Freeze(inner)
            | E::Dereference(inner)
            | E::Borrow(_, inner, _, _)
            | E::Cast(inner, _) => self.describe_exp(inner),
            E::BorrowLocal(_, var) => var.value().to_string(),
            E::UnaryExp(sp!(_, UnaryOp_::Not), inner) => format!("!{}", self.describe_exp(inner)),
            E::BinopExp(lhs, op, rhs) => {
                format!("{} {} {}", self.describe_exp(lhs), op.value.symbol(), self.describe_exp(rhs))
            }
            E::ModuleCall(call) => {
                let args = call
                    .arguments
                    .iter()
                    .map(|arg| self.describe_exp(arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}::{}({args})", call.module, call.name)
            }
            E::Multiple(values) => format!(
                "({})",
                values
                    .iter()
                    .map(|value| self.describe_exp(value))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            E::Unit { .. } => "()".to_string(),
            _ => format!("{:?}", exp.exp.value),
        }
    }

    fn borrow_field_name(&self, exp: &H::Exp) -> Option<(Loc, String)> {
        match &exp.exp.value {
            H::UnannotatedExp_::Borrow(_, inner, field, _) => {
                let inner_name = self.borrow_field_name(inner).map(|(_, text)| text);
                let field_text = field.to_string();
                Some((
                    exp.exp.loc,
                    match inner_name {
                        Some(inner) => format!("{inner}.{field_text}"),
                        None => field_text,
                    },
                ))
            }
            _ => None,
        }
    }
}

fn describe_value(value: &H::Value) -> String {
    match &value.value {
        H::Value_::U8(v) => format!("{v}u8"),
        H::Value_::U16(v) => format!("{v}u16"),
        H::Value_::U32(v) => format!("{v}u32"),
        H::Value_::U64(v) => format!("{v}u64"),
        H::Value_::U128(v) => format!("{v}u128"),
        H::Value_::U256(v) => format!("{v}u256"),
        H::Value_::Bool(v) => v.to_string(),
        _ => "value".to_string(),
    }
}

fn single_to_type(single: &H::SingleType) -> H::Type {
    move_ir_types::location::sp(single.loc, H::Type_::Single(single.clone()))
}

fn type_components(ty: &H::Type) -> Vec<H::Type> {
    match &ty.value {
        H::Type_::Unit => vec![],
        H::Type_::Single(_) => vec![ty.clone()],
        H::Type_::Multiple(values) => values.iter().map(single_to_type).collect(),
    }
}

fn checked_binary_interval(
    lhs: &Interval,
    rhs: &Interval,
    width: Option<u16>,
    op: fn(U256, U256) -> Option<U256>,
) -> Interval {
    let Some(width) = width else {
        return Interval::top();
    };
    let Some(lhs_lower) = lhs.lower else {
        return Interval {
            lower: Some(U256::zero()),
            upper: Some(uint_max(width)),
            bottom: false,
        };
    };
    let Some(lhs_upper) = lhs.upper else {
        return Interval {
            lower: Some(U256::zero()),
            upper: Some(uint_max(width)),
            bottom: false,
        };
    };
    let Some(rhs_lower) = rhs.lower else {
        return Interval {
            lower: Some(U256::zero()),
            upper: Some(uint_max(width)),
            bottom: false,
        };
    };
    let Some(rhs_upper) = rhs.upper else {
        return Interval {
            lower: Some(U256::zero()),
            upper: Some(uint_max(width)),
            bottom: false,
        };
    };
    match (op(lhs_lower, rhs_lower), op(lhs_upper, rhs_upper)) {
        (Some(lower), Some(upper)) => Interval {
            lower: Some(lower),
            upper: Some(upper.min(uint_max(width))),
            bottom: false,
        },
        _ => Interval {
            lower: Some(U256::zero()),
            upper: Some(uint_max(width)),
            bottom: false,
        },
    }
}
