use super::{RuleCtx, origin_key, single_param_index};
use crate::security_analysis::domain::{
    ObligationKind, ProofMode, RiskKind, RiskOrigin, ValueState,
};

/// Check whether a bitwise result (`&`, `|`, `^`) whose exact range is still
/// unknown feeds downstream arithmetic without an intermediate proof.
///
/// Returns `None` when the result is a known exact value (the bit-facts fully
/// determine it, so no precision has been lost).
pub fn check(
    ctx: &RuleCtx,
    result: &ValueState,
    result_text: &str,
) -> Option<RiskOrigin> {
    // If the exact value is determinable from bit-facts, the range is tight.
    if result.exact_value().is_some() {
        return None;
    }
    Some(RiskOrigin {
        key: origin_key(&RiskKind::SuspiciousBitwiseArithmetic, ctx.exp_loc),
        kind: RiskKind::SuspiciousBitwiseArithmetic,
        loc: ctx.exp_loc,
        source_param_index: single_param_index(result),
        width: result.width(),
        shift_amount: None,
        threshold: None,
        title: "Suspicious bitwise result reaches downstream arithmetic".to_string(),
        expr_text: result_text.to_string(),
        failed_condition: format!("exact range of {result_text} is known"),
        path_facts: ctx.path_facts.clone(),
        source_interval: result.interval.describe(),
        source_name: result_text.to_string(),
        helper_name: Some(ctx.fn_name.to_string()),
        helper_like: false,
        guard_mismatch: false,
        obligation_kind: ObligationKind::None,
        proof_mode: ProofMode::Heuristic,
        rounding_mode: None,
    })
}
