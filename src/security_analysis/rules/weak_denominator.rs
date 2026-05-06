use super::{RuleCtx, origin_key, single_param_index};
use crate::security_analysis::{
    SecurityMathMode,
    domain::{
        ExprOp, FormulaFactor, FormulaFacts, ObligationKind, ProofMode, RiskKind, RiskOrigin,
        SemanticRole, ValueState,
    },
    smt,
};
use move_core_types::u256::U256;
use move_ir_types::location::Loc;
use std::collections::BTreeSet;

/// Check whether the denominator of a division may be zero or, for a product
/// denominator, whether its independent factors are not all proven positive.
///
/// `numerator` and `denominator` are the abstract values at the division site.
/// `denominator_loc` is the source location of the denominator expression.
/// `denominator_text` is its human-readable text.
/// `is_denominator_helper` suppresses certain sink types for internal helpers.
/// `lhs_value` / `rhs_value` are the raw factor values — fed to the SMT
/// product-positivity lemma when both are available.
pub fn check(
    ctx: &RuleCtx,
    numerator: &ValueState,
    denominator: &ValueState,
    denominator_loc: Loc,
    denominator_text: &str,
    is_denominator_helper: bool,
    math_mode: SecurityMathMode,
    // Optional raw factor values for SMT product-positivity proof.
    lhs_factor: Option<&ValueState>,
    rhs_factor: Option<&ValueState>,
) -> Option<RiskOrigin> {
    // ── 1. Collect denominator factors ───────────────────────────────────────
    let denom_facts = denominator.formula_facts.as_ref();
    let mut factors = denom_facts
        .map(|facts| facts.factors.clone())
        .unwrap_or_default();
    factors.sort_by_key(|f| f.id);
    factors.dedup_by_key(|f| f.id);

    if factors.is_empty() {
        // Synthesise a single factor from the root expression or the text.
        let (id, name) = if let Some(root) = denom_facts.and_then(|f| f.root_expr.as_ref()) {
            (root.id, root.debug.clone())
        } else {
            (
                crate::security_analysis::domain::stable_hash(&[
                    b"synthetic-div-factor",
                    denominator_text.as_bytes(),
                    ctx.fn_name.as_bytes(),
                ]),
                denominator_text.to_string(),
            )
        };
        factors.push(FormulaFactor {
            id,
            name,
            tags: BTreeSet::new(),
            roles: BTreeSet::from([SemanticRole::DivRhs]),
            strict_positive: denominator
                .interval
                .lower
                .is_some_and(|lower| lower > U256::zero()),
            source_locs: vec![denominator_loc],
            proof_mode: if denom_facts.is_some() {
                ProofMode::Abstract
            } else {
                ProofMode::Heuristic
            },
        });
    }

    let is_product = denom_facts
        .and_then(|facts| facts.root_expr.as_ref())
        .is_some_and(|root| root.op == ExprOp::Mul)
        || factors.len() >= 2;

    // ── 2. Try SMT product-positivity discharge ───────────────────────────────
    // If both raw factors are available and proven strictly positive, the
    // product is provably non-zero — skip the finding.
    if is_product {
        if let (Some(lhs), Some(rhs)) = (lhs_factor, rhs_factor) {
            if smt::product::proven_strictly_positive(lhs, rhs) {
                return None;
            }
        }
    }

    // ── 3. Determine which obligation is violated ─────────────────────────────
    let all_factors_positive = factors.iter().all(|f| f.strict_positive);

    let zero_reachable = if all_factors_positive {
        false
    } else {
        denominator
            .interval
            .lower
            .is_none_or(|lower| lower == U256::zero())
    };

    let require_factor_positivity =
        is_product && invariant_mode_requires_factor_proofs(numerator, math_mode);
    let violates_non_zero = zero_reachable;
    let violates_factor_positivity = require_factor_positivity && !all_factors_positive;

    if !violates_non_zero && !violates_factor_positivity {
        return None;
    }

    let obligation_kind = if violates_non_zero {
        ObligationKind::NonZeroDivisor
    } else {
        ObligationKind::IndependentFactorPositivity
    };

    let failed_condition = match obligation_kind {
        ObligationKind::NonZeroDivisor => format!("{denominator_text} != 0"),
        ObligationKind::IndependentFactorPositivity => factors
            .iter()
            .map(|f| format!("{} > 0", factor_label(f)))
            .collect::<Vec<_>>()
            .join(" && "),
        _ => "denominator obligations hold".to_string(),
    };
    let title = match obligation_kind {
        ObligationKind::NonZeroDivisor => {
            "Denominator may be zero on a reachable value-bearing path"
        }
        ObligationKind::IndependentFactorPositivity => {
            "Independent denominator factors are not all proven strictly positive"
        }
        _ => "Potential denominator obligation failure",
    }
    .to_string();

    let proof_mode = if denom_facts.is_some() {
        ProofMode::Abstract
    } else {
        ProofMode::Heuristic
    };

    Some(RiskOrigin {
        key: origin_key(&RiskKind::ReachableWeakDenominator, ctx.exp_loc),
        kind: RiskKind::ReachableWeakDenominator,
        loc: ctx.exp_loc,
        source_param_index: single_param_index(denominator),
        width: denominator.width(),
        shift_amount: None,
        threshold: if violates_non_zero {
            Some(U256::zero())
        } else {
            None
        },
        title,
        expr_text: denominator_text.to_string(),
        failed_condition: failed_condition.clone(),
        path_facts: ctx.path_facts.clone(),
        source_interval: denominator.interval.describe(),
        source_name: denominator_text.to_string(),
        helper_name: Some(ctx.fn_name.to_string()),
        helper_like: is_denominator_helper,
        guard_mismatch: false,
        obligation_kind,
        proof_mode,
        rounding_mode: denom_facts.map(|f| f.rounding_mode),
    })
}

// ── helpers ───────────────────────────────────────────────────────────────────

fn factor_label(factor: &FormulaFactor) -> &str {
    if !factor.name.is_empty() {
        &factor.name
    } else {
        "factor"
    }
}

fn invariant_mode_requires_factor_proofs(
    numerator: &ValueState,
    math_mode: SecurityMathMode,
) -> bool {
    matches!(math_mode, SecurityMathMode::Deep)
        || numerator
            .formula_facts
            .as_ref()
            .is_some_and(|facts: &FormulaFacts| {
                !facts.factors.is_empty() || facts.root_expr.is_some()
            })
}
