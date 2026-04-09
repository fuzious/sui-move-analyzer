use super::{RuleCtx, origin_key, single_param_index};
use crate::security_analysis::domain::{
    ObligationKind, ProofMode, RiskKind, RiskOrigin, RoundingMode, ValueState, low_mask,
    width_mask,
};
use move_core_types::u256::U256;

/// Check whether `lhs >> shift_amount` silently discards non-zero low bits.
///
/// Returns `None` when bit-facts prove the discarded bits are all zero (i.e.,
/// the right-shift is exact).
pub fn check(
    ctx: &RuleCtx,
    lhs: &ValueState,
    lhs_text: &str,
    width: u16,
    shift_amount: u8,
) -> Option<RiskOrigin> {
    let discarded_mask = low_mask(shift_amount) & width_mask(width);
    if discarded_mask == U256::zero() {
        return None; // shifting by 0 is exact
    }
    if !lhs.may_have_non_zero_bits(discarded_mask) {
        return None; // bit-facts prove the low bits are zero
    }
    let failed_condition = format!("({lhs_text} & {discarded_mask}) == 0");
    Some(RiskOrigin {
        key: origin_key(&RiskKind::ReachableLossyRightShift, ctx.exp_loc),
        kind: RiskKind::ReachableLossyRightShift,
        loc: ctx.exp_loc,
        source_param_index: single_param_index(lhs),
        width: Some(width),
        shift_amount: Some(shift_amount),
        threshold: None,
        title: "Reachable lossy right shift on a value-bearing path".to_string(),
        expr_text: lhs_text.to_string(),
        failed_condition: failed_condition.clone(),
        path_facts: ctx.path_facts.clone(),
        source_interval: lhs.interval.describe(),
        source_name: lhs_text.to_string(),
        helper_name: Some(ctx.fn_name.to_string()),
        helper_like: false,
        guard_mismatch: false,
        obligation_kind: ObligationKind::None,
        proof_mode: ProofMode::Abstract,
        rounding_mode: Some(RoundingMode::RoundDown),
    })
}
