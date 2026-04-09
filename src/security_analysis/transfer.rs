use crate::security_analysis::{
    cfg::build_cfg,
    domain::{
        AbstractState, BitFacts, ConstraintOp, ExprNode, ExprOp, FormulaFactor, FormulaFacts,
        FormulaTag, Interval, ObligationKind, PathFact, ProofMode, RiskKind, RiskOrigin,
        RoundingMode, SemanticRole, SymbolicTerm, ValueState, builtin_width,
        formula_tags_from_field, formula_tags_from_function, formula_tags_from_name,
        integer_value, stable_hash, type_builtin, type_interval, uint_max, width_mask,
    },
    report::{SecurityFinding, SinkKind, collect_diagnostics, normalize_findings},
    rules::{
        self as rule_registry,
        RuleCtx,
        narrow_cast::cast_max,
        shift_truncation::no_truncation_threshold,
    },
    sinks::{classify_call_sink, sink_priority},
    smt,
    summaries::{FunctionSummary, ReturnSummary},
    SecurityMathMode,
};
use move_compiler::{
    cfgir::{ast as G, cfg::CFG},
    diagnostics::{Diagnostics, codes::Severity},
    expansion::ast::ModuleIdent,
    hlir::ast as H,
    parser::ast::{BinOp_, FunctionName, UnaryOp_},
    shared::files::MappedFiles,
};
use move_core_types::u256::U256;
use move_ir_types::location::Loc;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    path::{Path, PathBuf},
};

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
    math_mode: SecurityMathMode,
    smt_timeout_ms: u64,
}

impl<'a> ProgramAnalyzer<'a> {
    pub fn new(
        program: &'a G::Program,
        mapped_files: Option<&MappedFiles>,
        allowed_roots: Option<&[PathBuf]>,
        root_roots: Option<&[PathBuf]>,
        math_mode: SecurityMathMode,
        smt_timeout_ms: u64,
    ) -> Self {
        let mut functions = BTreeMap::new();
        let mut root_seed_keys = BTreeSet::new();
        for (module, module_def) in program.modules.key_cloned_iter() {
            for (function_name, function) in module_def.functions.key_cloned_iter() {
                let source_path = mapped_files
                    .map(|files| normalize_path(files.file_path(&function.loc.file_hash())));
                if let (Some(source_path), Some(allowed_roots)) = (&source_path, allowed_roots) {
                    if !path_in_scope(source_path, allowed_roots) {
                        continue;
                    }
                }
                let key = FunctionKey {
                    module,
                    name: function_name,
                };
                if let (Some(source_path), Some(root_roots)) = (&source_path, root_roots)
                    && path_in_scope(source_path, root_roots)
                {
                    root_seed_keys.insert(key.clone());
                }
                functions.insert(key.clone(), FunctionInfo { key, function });
            }
        }
        if !root_seed_keys.is_empty() {
            let reachable = reachable_functions(&functions, &root_seed_keys);
            functions.retain(|key, _| reachable.contains(key));
        }
        Self {
            functions,
            math_mode,
            smt_timeout_ms,
        }
    }

    pub fn run(&self) -> Diagnostics {
        collect_diagnostics(self.run_findings())
    }

    pub fn run_findings(&self) -> Vec<SecurityFinding> {
        let summaries = self.compute_summaries();
        let mut findings = vec![];
        for info in self.functions.values() {
            let mut analyzer =
                FunctionAnalyzer::new(info.clone(), &summaries, self.math_mode, self.smt_timeout_ms);
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
                let mut analyzer =
                    FunctionAnalyzer::new(info.clone(), &summaries, self.math_mode, self.smt_timeout_ms);
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

fn normalize_path(path: &Path) -> PathBuf {
    dunce::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

fn path_in_scope(path: &Path, allowed_roots: &[PathBuf]) -> bool {
    allowed_roots.iter().any(|root| path.starts_with(root))
}

fn reachable_functions<'a>(
    functions: &BTreeMap<FunctionKey, FunctionInfo<'a>>,
    seeds: &BTreeSet<FunctionKey>,
) -> BTreeSet<FunctionKey> {
    let mut reachable = BTreeSet::new();
    let mut worklist = VecDeque::from_iter(seeds.iter().cloned());
    while let Some(current) = worklist.pop_front() {
        if !reachable.insert(current.clone()) {
            continue;
        }
        let Some(info) = functions.get(&current) else {
            continue;
        };
        for callee in called_functions(info.function) {
            if functions.contains_key(&callee) && !reachable.contains(&callee) {
                worklist.push_back(callee);
            }
        }
    }
    reachable
}

fn called_functions(function: &G::Function) -> BTreeSet<FunctionKey> {
    let mut calls = BTreeSet::new();
    let G::FunctionBody_::Defined { blocks, .. } = &function.body.value else {
        return calls;
    };
    for block in blocks.values() {
        for command in block {
            collect_calls_from_command(command, &mut calls);
        }
    }
    calls
}

fn collect_calls_from_command(command: &H::Command, calls: &mut BTreeSet<FunctionKey>) {
    use H::Command_ as C;
    match &command.value {
        C::Assign(_, _, exp) => collect_calls_from_exp(exp, calls),
        C::Mutate(target, value) => {
            collect_calls_from_exp(target, calls);
            collect_calls_from_exp(value, calls);
        }
        C::Abort(_, exp) => collect_calls_from_exp(exp, calls),
        C::Return { exp, .. } => collect_calls_from_exp(exp, calls),
        C::IgnoreAndPop { exp, .. } => collect_calls_from_exp(exp, calls),
        C::Jump { .. } | C::Break(_) | C::Continue(_) => {}
        C::JumpIf { cond, .. } => collect_calls_from_exp(cond, calls),
        C::VariantSwitch { subject, .. } => collect_calls_from_exp(subject, calls),
    }
}

fn collect_calls_from_exp(exp: &H::Exp, calls: &mut BTreeSet<FunctionKey>) {
    use H::UnannotatedExp_ as E;
    match &exp.exp.value {
        E::ModuleCall(call) => {
            calls.insert(FunctionKey {
                module: call.module,
                name: call.name,
            });
            for argument in &call.arguments {
                collect_calls_from_exp(argument, calls);
            }
        }
        E::Freeze(inner) | E::Dereference(inner) | E::UnaryExp(_, inner) | E::Cast(inner, _) => {
            collect_calls_from_exp(inner, calls)
        }
        E::BinopExp(lhs, _, rhs) => {
            collect_calls_from_exp(lhs, calls);
            collect_calls_from_exp(rhs, calls);
        }
        E::Pack(_, _, fields) | E::PackVariant(_, _, _, fields) => {
            for (_, _, value) in fields {
                collect_calls_from_exp(value, calls);
            }
        }
        E::Multiple(values) | E::Vector(_, _, _, values) => {
            for value in values {
                collect_calls_from_exp(value, calls);
            }
        }
        E::Borrow(_, inner, _, _) => collect_calls_from_exp(inner, calls),
        E::Unit { .. }
        | E::Value(_)
        | E::Move { .. }
        | E::Copy { .. }
        | E::Constant(_)
        | E::ErrorConstant { .. }
        | E::BorrowLocal(_, _)
        | E::Unreachable
        | E::UnresolvedError => {}
    }
}

struct FunctionAnalyzer<'a> {
    info: FunctionInfo<'a>,
    summaries: &'a BTreeMap<FunctionKey, FunctionSummary>,
    local_types: BTreeMap<H::Var, H::Type>,
    current_outcome: AnalysisOutcome,
    mode: AnalysisMode,
    math_mode: SecurityMathMode,
    _smt_timeout_ms: u64,
}

impl<'a> FunctionAnalyzer<'a> {
    fn new(
        info: FunctionInfo<'a>,
        summaries: &'a BTreeMap<FunctionKey, FunctionSummary>,
        math_mode: SecurityMathMode,
        smt_timeout_ms: u64,
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
            math_mode,
            _smt_timeout_ms: smt_timeout_ms,
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
                if let Some((field_loc, field_name)) = self.borrow_field_name(target) {
                    for origin in &rhs.risky_origins {
                        self.emit_sink(
                            origin,
                            field_loc,
                            SinkKind::FieldWrite,
                            true,
                            state,
                            Some(field_name.clone()),
                        );
                    }
                    self.emit_rounding_mismatch_sink(
                        &rhs,
                        field_loc,
                        SinkKind::FieldWrite,
                        true,
                        state,
                        Some(field_name),
                    );
                }
                let _ = self.eval_exp(target, state);
            }
            C::Return { exp, .. } => {
                let values = self.eval_exp(exp, state);
                self.record_returns(&values);
                if self.is_publicish() {
                    let critical_api_surface = self.is_value_api_surface();
                    for value in values {
                        let sink_detail = Some(format!(
                            "returned from {}::{}",
                            self.info.key.module, self.info.key.name
                        ));
                        for origin in &value.risky_origins {
                            self.emit_sink(
                                origin,
                                command.loc,
                                SinkKind::PublicReturn,
                                critical_api_surface,
                                state,
                                sink_detail.clone(),
                            );
                        }
                        self.emit_rounding_mismatch_sink(
                            &value,
                            command.loc,
                            SinkKind::PublicReturn,
                            critical_api_surface,
                            state,
                            sink_detail,
                        );
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
        let Some(command) = blocks.get(&predecessor).and_then(|block| block.back()) else {
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
                    let mut constraints = self
                        .collect_constraints(lhs, true, state)
                        .unwrap_or_default();
                    constraints.extend(
                        self.collect_constraints(rhs, true, state)
                            .unwrap_or_default(),
                    );
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
                    let mut constraints = self
                        .collect_constraints(lhs, false, state)
                        .unwrap_or_default();
                    constraints.extend(
                        self.collect_constraints(rhs, false, state)
                            .unwrap_or_default(),
                    );
                    Some(constraints)
                }
                BinOp_::Lt | BinOp_::Le | BinOp_::Gt | BinOp_::Ge | BinOp_::Eq | BinOp_::Neq => {
                    self.comparison_constraint(lhs, op.value, rhs, truthy, state)
                        .map(|constraint| vec![constraint])
                }
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

        if let Some(merged) =
            self.merge_bounded_with_one_sided(left_var, &left_interval, &right_interval)
        {
            return Some(vec![merged]);
        }
        if let Some(merged) =
            self.merge_bounded_with_one_sided(left_var, &right_interval, &left_interval)
        {
            return Some(vec![merged]);
        }
        if let Some(merged) =
            self.merge_overlapping_bounded(left_var, &left_interval, &right_interval)
        {
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
        Some((
            var,
            op.clone(),
            bound,
            format!("{} {} {}", var.value(), op, bound),
        ))
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
            ConstraintOp::Ne => {
                let next = value.interval.clone();
                if next.bottom {
                    Interval::bottom()
                } else if next.is_singleton().is_some_and(|single| single == bound) {
                    Interval::bottom()
                } else if bound == U256::zero() {
                    // Unsigned Move integers are always >= 0, so `x != 0` implies `x >= 1`.
                    next.intersect(Some(U256::one()), None)
                } else if next.lower == Some(bound) {
                    if let Some(next_lower) = bound.checked_add(U256::one()) {
                        next.intersect(Some(next_lower), None)
                    } else {
                        Interval::bottom()
                    }
                } else if next.upper == Some(bound) {
                    if bound == U256::zero() {
                        Interval::bottom()
                    } else {
                        next.intersect(None, Some(bound - U256::one()))
                    }
                } else {
                    next
                }
            }
        };
        if value.interval.bottom {
            state.unreachable = true;
        } else {
            let strict_positive = value
                .interval
                .lower
                .is_some_and(|lower| lower > U256::zero());
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
            E::Borrow(_, inner, field, _) => {
                // ── Structural tagging from field name ───────────────────────
                // e.g. `pool.sqrt_price_a` tags the result as PriceLike even
                // when the receiving variable is named `val` or `p`.
                let mut values = self.eval_exp(inner, state);
                let field_tags = formula_tags_from_field(&field.to_string());
                if !field_tags.is_empty() {
                    for val in &mut values {
                        match &mut val.formula_facts {
                            Some(facts) => facts.merge_tags(field_tags.clone()),
                            None => {
                                val.formula_facts = Some(FormulaFacts {
                                    tags: field_tags.clone(),
                                    factors: vec![],
                                    root_expr: None,
                                    roles: BTreeSet::new(),
                                    rounding_mode: RoundingMode::Exact,
                                    rounding_trace: vec![],
                                    rounding_conflict: false,
                                });
                            }
                        }
                    }
                }
                values
            }
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
                .map(|value| {
                    self.eval_exp(value, state)
                        .into_iter()
                        .next()
                        .unwrap_or_else(ValueState::top)
                })
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
                    let ctx = self.rule_ctx(exp.exp.loc, state);
                    if let Some(origin) = rule_registry::narrow_cast::check(
                        &ctx,
                        &value,
                        &self.describe_exp(inner),
                        dest_width,
                    ) {
                        self.push_origin(&mut value, origin);
                    }
                    value.interval = value
                        .interval
                        .intersect(Some(U256::zero()), Some(max_value));
                    value.bit_facts = Some(
                        value
                            .bit_facts
                            .unwrap_or_else(|| BitFacts::unknown(dest_width)),
                    );
                    if let Some(facts) = &mut value.bit_facts {
                        facts.width = dest_width;
                        let mask = width_mask(dest_width);
                        facts.known_zero = facts.known_zero | (U256::max_value() ^ mask);
                        facts.known_one &= mask;
                    }
                    value.refine_with_bit_facts();
                }
                value
                    .risky_origins
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
        let callee_key = FunctionKey {
            module: call.module,
            name: call.name,
        };
        let callee_known = self.summaries.contains_key(&callee_key);
        if let Some(sink_kind) = classify_call_sink(call, callee_known) {
            for argument in &argument_values {
                let sink_detail = Some(format!(
                    "{}::{} [{}]",
                    call.module,
                    call.name,
                    sink_kind.label()
                ));
                for origin in &argument.risky_origins {
                    self.emit_sink(
                        origin,
                        exp.exp.loc,
                        SinkKind::CallArgument,
                        sink_kind.is_critical(),
                        state,
                        sink_detail.clone(),
                    );
                }
                self.emit_rounding_mismatch_sink(
                    argument,
                    exp.exp.loc,
                    SinkKind::CallArgument,
                    sink_kind.is_critical(),
                    state,
                    sink_detail,
                );
            }
        }

        let default_returns = type_components(&exp.ty)
            .into_iter()
            .map(|component| type_interval(&component))
            .collect::<Vec<_>>();
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
            let mut value = default_returns
                .get(index)
                .cloned()
                .unwrap_or_else(ValueState::top);
            let mut dependencies = BTreeSet::new();
            for dependency in &return_summary.parameter_dependencies {
                if let Some(argument) = argument_values.get(*dependency) {
                    dependencies.extend(argument.parameter_dependencies.iter().copied());
                    for origin in &argument.risky_origins {
                        if value
                            .risky_origins
                            .iter()
                            .all(|existing| existing.key != origin.key)
                        {
                            value.risky_origins.push(origin.clone());
                        }
                    }
                }
            }
            value.parameter_dependencies = dependencies;

            for origin in &return_summary.risky_origins {
                if let Some(param_index) = origin.source_param_index
                    && let Some(argument) = argument_values.get(param_index)
                    && self.origin_discharged_by_argument(origin, argument)
                {
                    continue;
                }
                let mut mapped_origin = origin.clone();
                mapped_origin.source_param_index = origin
                    .source_param_index
                    .and_then(|param_index| argument_values.get(param_index))
                    .and_then(|argument| self.single_parameter_dependency(argument));
                mapped_origin.helper_like = false;
                if value
                    .risky_origins
                    .iter()
                    .all(|existing| existing.key != mapped_origin.key)
                {
                    value.risky_origins.push(mapped_origin);
                }
            }
            if call_name.contains("mul") && argument_values.len() >= 2 {
                value.formula_facts = self.combine_mul_formula(
                    &argument_values[0],
                    &argument_values[1],
                    format!("{}::{}", call.module, call.name),
                );
            }
            if call_name.contains("div") && argument_values.len() >= 2 {
                value.formula_facts = self.combine_div_formula(
                    &argument_values[0],
                    &argument_values[1],
                    format!("{}::{}", call.module, call.name),
                );
                if let Some(origin) = self.make_weak_denominator_origin(
                    exp,
                    &argument_values[0],
                    &call.arguments[0],
                    &argument_values[1],
                    &call.arguments[1],
                    state,
                    Some(&argument_values[0]),
                    Some(&argument_values[1]),
                ) {
                    self.push_origin(&mut value, origin);
                }
            }
            let module_str = format!(
                "{}::{}",
                call.module.value.address.to_string().to_ascii_lowercase(),
                call.module.value.module.0.value.to_ascii_lowercase()
            );
            let structural_tags = formula_tags_from_function(&module_str, &call_name);
            if !structural_tags.is_empty() {
                match &mut value.formula_facts {
                    Some(facts) => facts.merge_tags(structural_tags),
                    None => {
                        let _id = stable_hash(&[
                            b"struct-tag",
                            call.module.value.module.0.value.as_str().as_bytes(),
                            call_name.as_bytes(),
                        ]);
                        value.formula_facts = Some(FormulaFacts {
                            tags: structural_tags,
                            factors: vec![],
                            root_expr: None,
                            roles: BTreeSet::new(),
                            rounding_mode: RoundingMode::Exact,
                            rounding_trace: vec![],
                            rounding_conflict: false,
                        });
                    }
                }
            }

            if let Some(facts) = &mut value.formula_facts {
                let lowered = call_name.to_ascii_lowercase();
                if lowered.contains("ceil")
                    || lowered.contains("round_up")
                    || lowered.contains("div_up")
                {
                    facts.rounding_mode = RoundingMode::RoundUp;
                    facts.rounding_trace.push(format!("{}::{} => round_up", call.module, call.name));
                } else if lowered.contains("floor")
                    || lowered.contains("round_down")
                    || lowered.contains("div_down")
                {
                    facts.rounding_mode = RoundingMode::RoundDown;
                    facts.rounding_trace.push(format!(
                        "{}::{} => round_down",
                        call.module, call.name
                    ));
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
        rhs_exp: &H::Exp,
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
                value.interval = checked_binary_interval(
                    &lhs.interval,
                    &rhs.interval,
                    result_width,
                    U256::checked_add,
                );
                value.bit_facts =
                    self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| {
                        l.checked_add(r)
                    });
                value.formula_facts = self.combine_add_formula(&lhs, &rhs, self.describe_exp(exp));
            }
            BinOp_::Sub => {
                value.interval = checked_binary_interval(
                    &lhs.interval,
                    &rhs.interval,
                    result_width,
                    U256::checked_sub,
                );
                value.bit_facts =
                    self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| {
                        l.checked_sub(r)
                    });
                value.formula_facts = self.combine_sub_formula(&lhs, &rhs, self.describe_exp(exp));
            }
            BinOp_::Mul => {
                value.interval = checked_binary_interval(
                    &lhs.interval,
                    &rhs.interval,
                    result_width,
                    U256::checked_mul,
                );
                value.bit_facts =
                    self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| {
                        l.checked_mul(r)
                    });
                value.formula_facts = self.combine_mul_formula(&lhs, &rhs, self.describe_exp(exp));
            }
            BinOp_::Div => {
                if rhs.interval.lower.is_some_and(|lower| lower > U256::zero())
                    && let (Some(lo), Some(hi), Some(rlo), Some(rhi)) = (
                        lhs.interval.lower,
                        lhs.interval.upper,
                        rhs.interval.lower,
                        rhs.interval.upper,
                    )
                {
                    value.interval = Interval {
                        lower: Some(lo / rhi),
                        upper: Some(hi / rlo),
                        bottom: false,
                    };
                } else {
                    value.interval = result_width.map_or_else(Interval::top, |width| Interval {
                        lower: Some(U256::zero()),
                        upper: Some(uint_max(width)),
                        bottom: false,
                    });
                }
                value.bit_facts =
                    self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| {
                        if r == U256::zero() {
                            None
                        } else {
                            l.checked_div(r)
                        }
                    });
                value.formula_facts = self.combine_div_formula(&lhs, &rhs, self.describe_exp(exp));
                if let Some(origin) = self.make_weak_denominator_origin(
                    exp, &lhs, lhs_exp, &rhs, rhs_exp, state,
                    Some(&lhs), Some(&rhs),
                ) {
                    self.push_origin(&mut value, origin);
                }
            }
            BinOp_::Mod => {
                value.interval = result_width.map_or_else(Interval::top, |width| Interval {
                    lower: Some(U256::zero()),
                    upper: Some(uint_max(width)),
                    bottom: false,
                });
                value.bit_facts =
                    self.derive_numeric_bit_facts(&lhs, &rhs, result_width, |l, r| {
                        if r == U256::zero() {
                            None
                        } else {
                            l.checked_rem(r)
                        }
                    });
                value.formula_facts = self.combine_mod_formula(&lhs, &rhs, self.describe_exp(exp));
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
                    let ctx = self.rule_ctx(exp.exp.loc, state);
                    if let Some(origin) = rule_registry::suspicious_bitwise::check(
                        &ctx, &value, &self.describe_exp(exp),
                    ) {
                        self.push_origin(&mut value, origin);
                    }
                }
                value.formula_facts =
                    self.combine_shift_formula(&lhs, &rhs, ExprOp::Shl, self.describe_exp(exp));
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
                    let ctx = self.rule_ctx(exp.exp.loc, state);
                    if let Some(origin) = rule_registry::suspicious_bitwise::check(
                        &ctx, &value, &self.describe_exp(exp),
                    ) {
                        self.push_origin(&mut value, origin);
                    }
                }
                value.formula_facts =
                    self.combine_shift_formula(&lhs, &rhs, ExprOp::Shr, self.describe_exp(exp));
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
                    let ctx = self.rule_ctx(exp.exp.loc, state);
                    if let Some(origin) = rule_registry::suspicious_bitwise::check(
                        &ctx, &value, &self.describe_exp(exp),
                    ) {
                        self.push_origin(&mut value, origin);
                    }
                }
                value.formula_facts = None;
            }
            BinOp_::Shl => {
                if let Some(width) = result_width {
                    let shift_amount = rhs.exact_value().map(|v| v.unchecked_as_u8());
                    if let Some(shift_amount) = shift_amount {
                        let ctx = self.rule_ctx(exp.exp.loc, state);
                        // ── Invalid shift count ──────────────────────────────
                        if let Some(origin) = rule_registry::invalid_shift_count::check(
                            &ctx, &rhs, width, shift_amount,
                        ) {
                            self.push_origin(&mut value, origin);
                            value.interval = Interval::top();
                            value.bit_facts = Some(BitFacts::unknown(width));
                        } else {
                            // ── Shift truncation / fake-checked-shift ────────
                            let threshold = no_truncation_threshold(width, shift_amount);
                            let guard_upper_bound = self.strongest_upper_bound(lhs_exp, state);
                            // Also ask SMT whether path constraints alone prove safety.
                            let lhs_var = self.extract_var(lhs_exp);
                            let var_facts: Vec<PathFact> = lhs_var
                                .map(|v| smt::path_facts_for_var(state, v))
                                .unwrap_or_default();
                            if smt::shift::proven_safe(
                                lhs.interval.upper,
                                threshold,
                                &var_facts,
                            ) {
                                // Provably safe — compute exact result.
                                if let (Some(lo), Some(hi)) =
                                    (lhs.interval.lower, lhs.interval.upper)
                                {
                                    value.interval = Interval {
                                        lower: lo.checked_shl(shift_amount as u32),
                                        upper: hi.checked_shl(shift_amount as u32),
                                        bottom: false,
                                    };
                                }
                                value.bit_facts = lhs
                                    .bit_facts
                                    .as_ref()
                                    .map(|facts| facts.shift_left(shift_amount, width));
                                value.refine_with_bit_facts();
                            } else if let Some(origin) = rule_registry::shift_truncation::check_shl(
                                &ctx,
                                &lhs,
                                &self.describe_exp(lhs_exp),
                                width,
                                shift_amount,
                                guard_upper_bound,
                            ) {
                                self.push_origin(&mut value, origin);
                                value.interval = Interval {
                                    lower: Some(U256::zero()),
                                    upper: result_max,
                                    bottom: false,
                                };
                                value.bit_facts = Some(BitFacts::unknown(width));
                            } else {
                                // Safe via interval (check_shl returned None).
                                if let (Some(lo), Some(hi)) =
                                    (lhs.interval.lower, lhs.interval.upper)
                                {
                                    value.interval = Interval {
                                        lower: lo.checked_shl(shift_amount as u32),
                                        upper: hi.checked_shl(shift_amount as u32),
                                        bottom: false,
                                    };
                                }
                                value.bit_facts = lhs
                                    .bit_facts
                                    .as_ref()
                                    .map(|facts| facts.shift_left(shift_amount, width));
                                value.refine_with_bit_facts();
                            }
                        }
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
                    let shift_amount = rhs.exact_value().map(|v| v.unchecked_as_u8());
                    if let Some(shift_amount) = shift_amount {
                        let ctx = self.rule_ctx(exp.exp.loc, state);
                        if let Some(origin) = rule_registry::invalid_shift_count::check(
                            &ctx, &rhs, width, shift_amount,
                        ) {
                            self.push_origin(&mut value, origin);
                            value.interval = Interval::top();
                            value.bit_facts = Some(BitFacts::unknown(width));
                        } else {
                            // Compute exact result.
                            if let (Some(lo), Some(hi)) = (lhs.interval.lower, lhs.interval.upper) {
                                value.interval = Interval {
                                    lower: lo.checked_shr(shift_amount as u32),
                                    upper: hi.checked_shr(shift_amount as u32),
                                    bottom: false,
                                };
                            }
                            value.bit_facts = lhs
                                .bit_facts
                                .as_ref()
                                .map(|facts| facts.shift_right(shift_amount, width));
                            value.refine_with_bit_facts();
                            // Check for lossy right-shift.
                            if let Some(origin) = rule_registry::lossy_right_shift::check(
                                &ctx,
                                &lhs,
                                &self.describe_exp(lhs_exp),
                                width,
                                shift_amount,
                            ) {
                                self.push_origin(&mut value, origin);
                            }
                        }
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
            BinOp_::Eq
            | BinOp_::Neq
            | BinOp_::Lt
            | BinOp_::Le
            | BinOp_::Gt
            | BinOp_::Ge
            | BinOp_::And
            | BinOp_::Or => {
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
            )
        });
        let suppress_suspicious =
            has_shift_or_precision_origin || matches!(op, BinOp_::Shl | BinOp_::Shr);
        if suppress_suspicious {
            value
                .risky_origins
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
            self.emit_arithmetic_use(
                &lhs.risky_origins,
                exp.exp.loc,
                state,
                detail.clone(),
                suppress_suspicious,
            );
            self.emit_arithmetic_use(
                &rhs.risky_origins,
                exp.exp.loc,
                state,
                detail,
                suppress_suspicious,
            );
            self.emit_rounding_mismatch_sink(
                &lhs,
                exp.exp.loc,
                SinkKind::ArithmeticUse,
                false,
                state,
                Some(self.describe_exp(exp)),
            );
            self.emit_rounding_mismatch_sink(
                &rhs,
                exp.exp.loc,
                SinkKind::ArithmeticUse,
                false,
                state,
                Some(self.describe_exp(exp)),
            );
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

    fn combine_add_formula(
        &self,
        lhs: &ValueState,
        rhs: &ValueState,
        expression_debug: String,
    ) -> Option<FormulaFacts> {
        let lhs_facts = lhs.formula_facts.as_ref();
        let rhs_facts = rhs.formula_facts.as_ref();
        if lhs_facts.is_none() && rhs_facts.is_none() {
            return None;
        }
        Some(FormulaFacts {
            tags: self.union_formula_tags(lhs_facts, rhs_facts),
            factors: self.merge_formula_factors(lhs_facts, rhs_facts),
            root_expr: self.make_binary_expr(ExprOp::Add, lhs, rhs, expression_debug, true),
            roles: BTreeSet::new(),
            rounding_mode: self.merge_rounding_mode(lhs_facts, rhs_facts),
            rounding_trace: self.merge_rounding_trace(lhs_facts, rhs_facts, "add"),
            rounding_conflict: false,
        })
    }

    fn combine_sub_formula(
        &self,
        lhs: &ValueState,
        rhs: &ValueState,
        expression_debug: String,
    ) -> Option<FormulaFacts> {
        let lhs_facts = lhs.formula_facts.as_ref();
        let rhs_facts = rhs.formula_facts.as_ref();
        if lhs_facts.is_none() && rhs_facts.is_none() {
            return None;
        }
        let mut tags = self.union_formula_tags(lhs_facts, rhs_facts);
        if lhs_facts
            .is_some_and(|facts| facts.tags.contains(&FormulaTag::PriceLike))
            && rhs_facts.is_some_and(|facts| facts.tags.contains(&FormulaTag::PriceLike))
        {
            tags.insert(FormulaTag::PriceDiff);
        }
        let mut facts = FormulaFacts {
            tags,
            factors: self.merge_formula_factors(lhs_facts, rhs_facts),
            root_expr: self.make_binary_expr(ExprOp::Sub, lhs, rhs, expression_debug, false),
            roles: BTreeSet::from([SemanticRole::Difference]),
            rounding_mode: self.merge_rounding_mode(lhs_facts, rhs_facts),
            rounding_trace: self.merge_rounding_trace(lhs_facts, rhs_facts, "sub"),
            rounding_conflict: false,
        };
        facts.add_role(SemanticRole::Difference);
        Some(facts)
    }

    fn combine_mul_formula(
        &self,
        lhs: &ValueState,
        rhs: &ValueState,
        expression_debug: String,
    ) -> Option<FormulaFacts> {
        let lhs_facts = lhs.formula_facts.as_ref();
        let rhs_facts = rhs.formula_facts.as_ref();
        if lhs_facts.is_none() && rhs_facts.is_none() {
            return None;
        }
        let mut tags = self.union_formula_tags(lhs_facts, rhs_facts);
        if lhs_facts
            .is_some_and(|facts| facts.tags.contains(&FormulaTag::PriceLike))
            && rhs_facts.is_some_and(|facts| facts.tags.contains(&FormulaTag::PriceLike))
        {
            tags.insert(FormulaTag::PriceProduct);
            tags.insert(FormulaTag::DenominatorLike);
        }
        let mut facts = FormulaFacts {
            tags,
            factors: self.merge_formula_factors(lhs_facts, rhs_facts),
            root_expr: self.make_binary_expr(ExprOp::Mul, lhs, rhs, expression_debug, true),
            roles: BTreeSet::from([SemanticRole::MulFactor]),
            rounding_mode: self.merge_rounding_mode(lhs_facts, rhs_facts),
            rounding_trace: self.merge_rounding_trace(lhs_facts, rhs_facts, "mul"),
            rounding_conflict: false,
        };
        facts.add_role(SemanticRole::MulFactor);
        Some(facts)
    }

    fn combine_div_formula(
        &self,
        lhs: &ValueState,
        rhs: &ValueState,
        expression_debug: String,
    ) -> Option<FormulaFacts> {
        let lhs_facts = lhs.formula_facts.as_ref();
        let rhs_facts = rhs.formula_facts.as_ref();
        if lhs_facts.is_none() && rhs_facts.is_none() {
            return None;
        }
        let mut facts = FormulaFacts {
            tags: self.union_formula_tags(lhs_facts, rhs_facts),
            factors: self.merge_formula_factors(lhs_facts, rhs_facts),
            root_expr: self.make_binary_expr(ExprOp::Div, lhs, rhs, expression_debug, false),
            roles: BTreeSet::from([SemanticRole::DivLhs, SemanticRole::DivRhs]),
            rounding_mode: RoundingMode::RoundDown,
            rounding_trace: self.merge_rounding_trace(lhs_facts, rhs_facts, "div/floor"),
            rounding_conflict: false,
        };
        facts.add_role(SemanticRole::DivLhs);
        facts.add_role(SemanticRole::DivRhs);
        Some(facts)
    }

    fn combine_mod_formula(
        &self,
        lhs: &ValueState,
        rhs: &ValueState,
        expression_debug: String,
    ) -> Option<FormulaFacts> {
        let lhs_facts = lhs.formula_facts.as_ref();
        let rhs_facts = rhs.formula_facts.as_ref();
        if lhs_facts.is_none() && rhs_facts.is_none() {
            return None;
        }
        let mut facts = FormulaFacts {
            tags: self.union_formula_tags(lhs_facts, rhs_facts),
            factors: self.merge_formula_factors(lhs_facts, rhs_facts),
            root_expr: self.make_binary_expr(ExprOp::Mod, lhs, rhs, expression_debug, false),
            roles: BTreeSet::from([SemanticRole::DivRhs]),
            rounding_mode: RoundingMode::RoundDown,
            rounding_trace: self.merge_rounding_trace(lhs_facts, rhs_facts, "mod/floor"),
            rounding_conflict: false,
        };
        facts.add_role(SemanticRole::DivRhs);
        Some(facts)
    }

    fn combine_shift_formula(
        &self,
        lhs: &ValueState,
        rhs: &ValueState,
        op: ExprOp,
        expression_debug: String,
    ) -> Option<FormulaFacts> {
        let lhs_facts = lhs.formula_facts.as_ref();
        let rhs_facts = rhs.formula_facts.as_ref();
        if lhs_facts.is_none() && rhs_facts.is_none() {
            return None;
        }
        let rounding_mode = if op == ExprOp::Shr {
            RoundingMode::RoundDown
        } else {
            self.merge_rounding_mode(lhs_facts, rhs_facts)
        };
        let trace = if op == ExprOp::Shr {
            "shr/floor"
        } else {
            "shl/scale"
        };
        let mut facts = FormulaFacts {
            tags: self.union_formula_tags(lhs_facts, rhs_facts),
            factors: self.merge_formula_factors(lhs_facts, rhs_facts),
            root_expr: self.make_binary_expr(op, lhs, rhs, expression_debug, false),
            roles: BTreeSet::from([SemanticRole::Pow2Scale]),
            rounding_mode,
            rounding_trace: self.merge_rounding_trace(lhs_facts, rhs_facts, trace),
            rounding_conflict: false,
        };
        facts.add_role(SemanticRole::Pow2Scale);
        Some(facts)
    }

    fn union_formula_tags(
        &self,
        lhs: Option<&FormulaFacts>,
        rhs: Option<&FormulaFacts>,
    ) -> BTreeSet<FormulaTag> {
        let mut tags = BTreeSet::new();
        if let Some(lhs) = lhs {
            tags.extend(lhs.tags.iter().cloned());
        }
        if let Some(rhs) = rhs {
            tags.extend(rhs.tags.iter().cloned());
        }
        tags
    }

    fn merge_formula_factors(
        &self,
        lhs: Option<&FormulaFacts>,
        rhs: Option<&FormulaFacts>,
    ) -> Vec<FormulaFactor> {
        let mut factors: Vec<FormulaFactor> = vec![];
        for source in [lhs, rhs].into_iter().flatten() {
            for factor in &source.factors {
                if let Some(existing) = factors.iter_mut().find(|known| known.id == factor.id) {
                    existing.strict_positive &= factor.strict_positive;
                    existing.tags.extend(factor.tags.iter().cloned());
                    existing.roles.extend(factor.roles.iter().cloned());
                    for loc in &factor.source_locs {
                        if !existing.source_locs.contains(loc) {
                            existing.source_locs.push(*loc);
                        }
                    }
                    if existing.proof_mode != factor.proof_mode {
                        existing.proof_mode = ProofMode::Heuristic;
                    }
                } else {
                    factors.push(factor.clone());
                }
            }
        }
        factors
    }

    fn merge_rounding_mode(
        &self,
        lhs: Option<&FormulaFacts>,
        rhs: Option<&FormulaFacts>,
    ) -> RoundingMode {
        match (lhs.map(|facts| facts.rounding_mode), rhs.map(|facts| facts.rounding_mode)) {
            (Some(left), Some(right)) if left == right => left,
            (Some(RoundingMode::Exact), Some(other)) => other,
            (Some(other), Some(RoundingMode::Exact)) => other,
            (Some(_), Some(_)) => RoundingMode::Unknown,
            (Some(single), None) | (None, Some(single)) => single,
            (None, None) => RoundingMode::Exact,
        }
    }

    fn merge_rounding_trace(
        &self,
        lhs: Option<&FormulaFacts>,
        rhs: Option<&FormulaFacts>,
        tail: &str,
    ) -> Vec<String> {
        let mut trace = vec![];
        for source in [lhs, rhs].into_iter().flatten() {
            for item in &source.rounding_trace {
                if !trace.contains(item) {
                    trace.push(item.clone());
                }
            }
        }
        if !tail.is_empty() {
            trace.push(tail.to_string());
        }
        trace
    }

    fn root_expr_from_value(&self, value: &ValueState) -> Option<ExprNode> {
        if let Some(facts) = &value.formula_facts
            && let Some(expr) = &facts.root_expr
        {
            return Some(expr.clone());
        }
        value.exact_value().map(|constant| {
            let debug = constant.to_string();
            ExprNode {
                id: stable_hash(&[b"const", debug.as_bytes()]),
                op: ExprOp::Const,
                children: vec![],
                debug,
            }
        })
    }

    fn make_binary_expr(
        &self,
        op: ExprOp,
        lhs: &ValueState,
        rhs: &ValueState,
        debug: String,
        commutative: bool,
    ) -> Option<ExprNode> {
        let lhs = self.root_expr_from_value(lhs)?;
        let rhs = self.root_expr_from_value(rhs)?;
        let mut children = vec![lhs.id, rhs.id];
        if commutative {
            children.sort_unstable();
        }
        let op_name = format!("{op:?}");
        let child_strings = children
            .iter()
            .map(|id| id.to_string().into_bytes())
            .collect::<Vec<_>>();
        let mut hash_parts = vec![op_name.as_bytes()];
        for child in &child_strings {
            hash_parts.push(child.as_slice());
        }
        let id = stable_hash(&hash_parts);
        Some(ExprNode {
            id,
            op,
            children,
            debug,
        })
    }

    fn make_weak_denominator_origin(
        &self,
        exp: &H::Exp,
        numerator: &ValueState,
        _numerator_exp: &H::Exp,
        denominator: &ValueState,
        denominator_exp: &H::Exp,
        state: &AbstractState,
        lhs_factor: Option<&ValueState>,
        rhs_factor: Option<&ValueState>,
    ) -> Option<RiskOrigin> {
        let ctx = self.rule_ctx(exp.exp.loc, state);
        rule_registry::weak_denominator::check(
            &ctx,
            numerator,
            denominator,
            denominator_exp.exp.loc,
            &self.describe_exp(denominator_exp),
            self.is_denominator_helper_context(),
            self.math_mode,
            lhs_factor,
            rhs_factor,
        )
    }

    fn is_denominator_helper_context(&self) -> bool {
        if self.info.function.entry.is_some() {
            return false;
        }
        let lowered = self.info.key.name.to_string().to_ascii_lowercase();
        lowered.contains("div")
            || lowered.contains("quotient")
            || lowered.contains("checked")
            || lowered.contains("mul_shr")
    }

    /// Build a `RuleCtx` for the current program point.
    fn rule_ctx(&self, exp_loc: Loc, state: &AbstractState) -> RuleCtx<'_> {
        RuleCtx {
            exp_loc,
            fn_name: self.info.key.name.0.value.as_str(),
            path_facts: self.path_fact_texts(state),
        }
    }

    fn describe_obligation(&self, obligation_kind: ObligationKind) -> &'static str {
        match obligation_kind {
            ObligationKind::None => "none",
            ObligationKind::NonZeroDivisor => "divisor must be non-zero",
            ObligationKind::IndependentFactorPositivity => {
                "each independent denominator factor must be strictly positive"
            }
            ObligationKind::RoundingConsistency => {
                "rounding mode must be consistent for semantically related quantities"
            }
        }
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

    fn emit_rounding_mismatch_sink(
        &mut self,
        value: &ValueState,
        sink_loc: Loc,
        sink_kind: SinkKind,
        financial: bool,
        state: &AbstractState,
        detail: Option<String>,
    ) {
        let Some(facts) = &value.formula_facts else {
            return;
        };
        if !facts.rounding_conflict {
            return;
        }
        if facts.factors.is_empty() && facts.root_expr.is_none() {
            return;
        }
        let root_id = facts.root_expr.as_ref().map(|root| root.id).unwrap_or_default();
        let mut sink_detail = detail.unwrap_or_default();
        if !facts.rounding_trace.is_empty() {
            if !sink_detail.is_empty() {
                sink_detail.push_str("; ");
            }
            sink_detail.push_str(&format!(
                "rounding trace: {}",
                facts.rounding_trace.join(" -> ")
            ));
        }
        let origin = RiskOrigin {
            key: format!(
                "{}:{}:{}:{}",
                RiskKind::ReachableRoundingMismatch.rule_id(),
                sink_loc.file_hash(),
                sink_loc.start(),
                root_id
            ),
            kind: RiskKind::ReachableRoundingMismatch,
            loc: sink_loc,
            source_param_index: self.single_parameter_dependency(value),
            width: value.width(),
            shift_amount: None,
            threshold: None,
            title: "Semantically related value reaches sink with incompatible rounding modes"
                .to_string(),
            expr_text: if sink_detail.is_empty() {
                "value".to_string()
            } else {
                sink_detail.clone()
            },
            failed_condition:
                "consistent rounding mode across all reachable paths for this quantity".to_string(),
            path_facts: self.path_fact_texts(state),
            source_interval: value.interval.describe(),
            source_name: facts
                .root_expr
                .as_ref()
                .map(|root| root.debug.clone())
                .unwrap_or_else(|| "value".to_string()),
            helper_name: Some(self.info.key.name.to_string()),
            helper_like: false,
            guard_mismatch: false,
            obligation_kind: ObligationKind::RoundingConsistency,
            proof_mode: ProofMode::Abstract,
            rounding_mode: Some(facts.rounding_mode),
        };
        self.emit_sink(
            &origin,
            sink_loc,
            sink_kind,
            financial,
            state,
            if sink_detail.is_empty() {
                None
            } else {
                Some(sink_detail)
            },
        );
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
        if origin.kind == RiskKind::ReachableWeakDenominator
            && origin.helper_like
            && matches!(sink_kind, SinkKind::PublicReturn | SinkKind::ArithmeticUse)
        {
            return;
        }
        let priority = sink_priority(&sink_kind, financial);
        let severity = match origin.kind {
            RiskKind::SuspiciousBitwiseArithmetic => Severity::Warning,
            RiskKind::ReachableLossyRightShift => {
                if priority >= 3 {
                    Severity::NonblockingError
                } else {
                    Severity::Warning
                }
            }
            RiskKind::ReachableWeakDenominator => {
                if origin.threshold == Some(U256::zero())
                    && priority >= 1
                    && origin.proof_mode != ProofMode::Heuristic
                {
                    Severity::NonblockingError
                } else {
                    Severity::Warning
                }
            }
            RiskKind::ReachableRoundingMismatch => {
                if priority >= 1 {
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
            RiskKind::ReachableShiftTruncation => {
                "Reachable truncating left shift on a value-bearing path"
            }
            RiskKind::FakeCheckedShift => {
                "Custom checked-shift helper may be unsound on a reachable path"
            }
            RiskKind::ReachableNarrowCast => {
                "Reachable narrowing cast may fail on a value-bearing path"
            }
            RiskKind::InvalidShiftCount => "Reachable invalid shift count",
            RiskKind::ReachableLossyRightShift => {
                "Reachable lossy right shift on a value-bearing path"
            }
            RiskKind::SuspiciousBitwiseArithmetic => {
                "Suspicious bitwise result reaches downstream arithmetic"
            }
            RiskKind::ReachableWeakDenominator => origin.title.as_str(),
            RiskKind::ReachableRoundingMismatch => origin.title.as_str(),
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
        message.push_str(&format!(
            " Obligation: {}. Evidence: {:?}.",
            self.describe_obligation(origin.obligation_kind.clone()),
            origin.proof_mode
        ));
        if let Some(rounding_mode) = origin.rounding_mode {
            message.push_str(&format!(" Rounding mode seen: {:?}.", rounding_mode));
        }
        if origin.guard_mismatch {
            message.push_str(" A dominating helper guard exists, but it is weaker than the true no-truncation bound.");
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
            RiskKind::SuspiciousBitwiseArithmetic => {
                "Prove the masked or combined bit range before reusing the value in arithmetic or sink-bearing logic.".to_string()
            }
            RiskKind::ReachableWeakDenominator => {
                "Prove `divisor != 0` on all paths and, for product denominators, prove each independent factor is strictly positive.".to_string()
            }
            RiskKind::ReachableRoundingMismatch => {
                "Use one rounding policy for this quantity (all floor or all ceil), or add an explicit compensation invariant before the sink.".to_string()
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
        state.locals.get(var).cloned().unwrap_or_else(|| {
            self.local_types
                .get(var)
                .map(type_interval)
                .unwrap_or_else(ValueState::top)
        })
    }

    fn annotate_value_with_name(&self, value: &mut ValueState, name: &str) {
        let strict_positive = value
            .interval
            .lower
            .is_some_and(|lower| lower > U256::zero());
        let tags = formula_tags_from_name(name);
        let id = stable_hash(&[b"var", name.as_bytes()]);
        match &mut value.formula_facts {
            Some(facts) => {
                if !tags.is_empty() {
                    facts.merge_tags(tags.clone());
                }
                if let Some(existing) = facts.factors.iter_mut().find(|factor| factor.id == id) {
                    existing.strict_positive = strict_positive;
                    existing.tags.extend(tags);
                } else if facts.factors.is_empty() {
                    facts.factors.push(FormulaFactor::new(
                        id,
                        name.to_string(),
                        tags,
                        strict_positive,
                        ProofMode::Abstract,
                    ));
                }
                if facts.root_expr.is_none() {
                    facts.root_expr = Some(ExprNode {
                        id,
                        op: ExprOp::Var,
                        children: vec![],
                        debug: name.to_string(),
                    });
                }
            }
            None => {
                value.formula_facts = Some(FormulaFacts {
                    tags: tags.clone(),
                    factors: vec![FormulaFactor::new(
                        id,
                        name.to_string(),
                        tags,
                        strict_positive,
                        ProofMode::Abstract,
                    )],
                    root_expr: Some(ExprNode {
                        id,
                        op: ExprOp::Var,
                        children: vec![],
                        debug: name.to_string(),
                    }),
                    roles: BTreeSet::new(),
                    rounding_mode: RoundingMode::Exact,
                    rounding_trace: vec![],
                    rounding_conflict: false,
                });
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
        !matches!(self.info.function.visibility, H::Visibility::Internal)
            || self.info.function.entry.is_some()
    }

    fn is_value_api_surface(&self) -> bool {
        self.info.function.entry.is_some() || self.info.function.signature.parameters.len() >= 2
    }

    fn single_parameter_dependency(&self, value: &ValueState) -> Option<usize> {
        if value.parameter_dependencies.len() == 1 {
            value.parameter_dependencies.iter().next().copied()
        } else {
            None
        }
    }

    fn origin_discharged_by_argument(&self, origin: &RiskOrigin, argument: &ValueState) -> bool {
        match origin.obligation_kind {
            ObligationKind::NonZeroDivisor => argument
                .interval
                .lower
                .is_some_and(|lower| lower > U256::zero())
                || argument
                    .formula_facts
                    .as_ref()
                    .is_some_and(FormulaFacts::all_factors_strict_positive),
            ObligationKind::IndependentFactorPositivity => argument
                .formula_facts
                .as_ref()
                .is_some_and(FormulaFacts::all_factors_strict_positive),
            _ => origin.threshold.is_some_and(|threshold| {
                argument
                    .interval
                    .upper
                    .is_some_and(|upper| upper <= threshold)
            }),
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
        state
            .path_facts
            .iter()
            .map(|fact| fact.text.clone())
            .collect()
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
                format!(
                    "{} {} {}",
                    self.describe_exp(lhs),
                    op.value.symbol(),
                    self.describe_exp(rhs)
                )
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
