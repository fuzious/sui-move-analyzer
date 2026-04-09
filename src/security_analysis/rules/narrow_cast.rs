use super::{RuleCtx, origin_key, single_param_index};
use crate::security_analysis::domain::{
    ObligationKind, ProofMode, RiskKind, RiskOrigin, ValueState, uint_max,
};
use move_core_types::u256::U256;

/// Maximum value representable in a `width`-bit integer.
pub fn cast_max(width: u16) -> U256 {
    uint_max(width)
}

/// Check whether casting `source` to `dest_width` bits may abort at runtime.
///
/// Returns `None` when the source interval is already within `[0, dest_max]`.
pub fn check(
    ctx: &RuleCtx,
    source: &ValueState,
    source_text: &str,
    dest_width: u16,
) -> Option<RiskOrigin> {
    let max_value = cast_max(dest_width);
    if source.interval.upper.is_some_and(|upper| upper <= max_value) {
        return None;
    }
    let failed_condition = format!("{source_text} <= {max_value}");
    Some(RiskOrigin {
        key: origin_key(&RiskKind::ReachableNarrowCast, ctx.exp_loc),
        kind: RiskKind::ReachableNarrowCast,
        loc: ctx.exp_loc,
        source_param_index: single_param_index(source),
        width: Some(dest_width),
        shift_amount: None,
        threshold: Some(max_value),
        title: "Reachable narrowing cast on value-bearing path".to_string(),
        expr_text: source_text.to_string(),
        failed_condition: failed_condition.clone(),
        path_facts: ctx.path_facts.clone(),
        source_interval: source.interval.describe(),
        source_name: source_text.to_string(),
        helper_name: Some(ctx.fn_name.to_string()),
        helper_like: false,
        guard_mismatch: false,
        obligation_kind: ObligationKind::None,
        proof_mode: ProofMode::Abstract,
        rounding_mode: None,
    })
}
