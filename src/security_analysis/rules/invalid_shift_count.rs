use super::{RuleCtx, origin_key, single_param_index};
use crate::security_analysis::domain::{ObligationKind, ProofMode, RiskKind, RiskOrigin, ValueState};

/// Check whether a shift by `shift_amount` bits on a `width`-bit type is
/// always invalid (shift count >= type width, which aborts at runtime).
///
/// Returns `None` when the shift count is strictly less than `width`.
pub fn check(
    ctx: &RuleCtx,
    rhs: &ValueState,
    width: u16,
    shift_amount: u8,
) -> Option<RiskOrigin> {
    if (shift_amount as u16) < width {
        return None;
    }
    let failed_condition = format!("{shift_amount} < {width}");
    Some(RiskOrigin {
        key: origin_key(&RiskKind::InvalidShiftCount, ctx.exp_loc),
        kind: RiskKind::InvalidShiftCount,
        loc: ctx.exp_loc,
        source_param_index: single_param_index(rhs),
        width: Some(width),
        shift_amount: Some(shift_amount),
        threshold: None,
        title: "Reachable invalid shift count".to_string(),
        expr_text: format!("shift by {shift_amount}"),
        failed_condition: failed_condition.clone(),
        path_facts: ctx.path_facts.clone(),
        source_interval: rhs.interval.describe(),
        source_name: format!("{shift_amount}"),
        helper_name: Some(ctx.fn_name.to_string()),
        helper_like: false,
        guard_mismatch: false,
        obligation_kind: ObligationKind::None,
        proof_mode: ProofMode::Abstract,
        rounding_mode: None,
    })
}
