use super::{RuleCtx, origin_key, single_param_index};
use crate::security_analysis::domain::{
    ObligationKind, ProofMode, RiskKind, RiskOrigin, ValueState, uint_max,
};
use move_core_types::u256::U256;

/// The maximum value that can be left-shifted by `shift` bits in a `width`-bit
/// type without losing any bits: `MAX_U{width} >> shift`.
pub fn no_truncation_threshold(width: u16, shift: u8) -> U256 {
    uint_max(width) >> shift
}

/// Check whether `lhs << shift_amount` may truncate high bits.
///
/// Returns `None` when the shift is provably safe.  Returns a `RiskOrigin`
/// with kind `FakeCheckedShift` when a guard exists but is too weak, or
/// `ReachableShiftTruncation` when no guard is present.
pub fn check_shl(
    ctx: &RuleCtx,
    lhs: &ValueState,
    lhs_text: &str,
    width: u16,
    shift_amount: u8,
    // Strongest upper bound that path constraints place on the operand.
    guard_upper_bound: Option<U256>,
) -> Option<RiskOrigin> {
    let threshold = no_truncation_threshold(width, shift_amount);

    // Interval already proves safety — no finding.
    if lhs.interval.upper.is_some_and(|upper| upper <= threshold) {
        return None;
    }

    let has_guard = guard_upper_bound.is_some();
    let guard_mismatch = super::fake_checked_shift::guard_is_weaker_than_threshold(
        guard_upper_bound,
        threshold,
    );

    let kind = if has_guard && guard_mismatch {
        RiskKind::FakeCheckedShift
    } else {
        RiskKind::ReachableShiftTruncation
    };

    let failed_condition =
        format!("{lhs_text} <= {threshold} (MAX_U{width} >> {shift_amount})");
    let title = if has_guard && guard_mismatch {
        "Custom checked-shift helper may be unsound on a reachable path".to_string()
    } else {
        "Reachable truncating left shift on a value-bearing path".to_string()
    };
    let extra = if guard_mismatch {
        " A dominating helper guard exists, but it is weaker than the \
         true no-truncation bound."
    } else {
        ""
    };
    let _message = format!(
        "{lhs_text}. The analyzer cannot prove `{failed_condition}`. \
         Path facts: {}. Source interval: {}.{extra}",
        if ctx.path_facts.is_empty() {
            "none".to_string()
        } else {
            ctx.path_facts.join(", ")
        },
        lhs.interval.describe(),
    );

    Some(RiskOrigin {
        key: origin_key(&kind, ctx.exp_loc),
        kind,
        loc: ctx.exp_loc,
        source_param_index: single_param_index(lhs),
        width: Some(width),
        shift_amount: Some(shift_amount),
        threshold: Some(threshold),
        title,
        expr_text: lhs_text.to_string(),
        failed_condition,
        path_facts: ctx.path_facts.clone(),
        source_interval: lhs.interval.describe(),
        source_name: lhs_text.to_string(),
        helper_name: Some(ctx.fn_name.to_string()),
        helper_like: false,
        guard_mismatch,
        obligation_kind: ObligationKind::None,
        proof_mode: ProofMode::Abstract,
        rounding_mode: None,
    })
}
