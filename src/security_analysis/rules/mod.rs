pub mod fake_checked_shift;
pub mod invalid_shift_count;
pub mod lossy_right_shift;
pub mod narrow_cast;
pub mod rounding_mismatch;
pub mod shift_truncation;
pub mod suspicious_bitwise;
pub mod weak_denominator;

use crate::security_analysis::domain::{RiskKind, ValueState};
use move_ir_types::location::Loc;

/// Context shared by every rule check.  Rules receive this plus their own
/// operation-specific inputs.  Keeping this slim avoids coupling rules to the
/// entire `FunctionAnalyzer` internals.
pub struct RuleCtx<'a> {
    /// Source location of the expression being checked.
    pub exp_loc: Loc,
    /// Human-readable name of the current function (for messages and keys).
    pub fn_name: &'a str,
    /// Path facts active at this program point (already rendered as strings).
    pub path_facts: Vec<String>,
}

/// Extract the single parameter index that `value` depends on, or `None` if
/// it depends on zero or multiple parameters.  Used when building `RiskOrigin`
/// to preserve cross-function taint provenance.
pub(super) fn single_param_index(value: &ValueState) -> Option<usize> {
    if value.parameter_dependencies.len() == 1 {
        value.parameter_dependencies.iter().next().copied()
    } else {
        None
    }
}

/// Build the deduplication key used by `normalize_findings`.
pub(super) fn origin_key(kind: &RiskKind, loc: Loc) -> String {
    format!("{}:{}:{}", kind.rule_id(), loc.file_hash(), loc.start())
}

/// Trait implemented by every rule struct.  Provides a registry entry (id,
/// kind, description) independently of the check functions whose signatures
/// vary per rule.
pub trait Rule: Send + Sync {
    fn rule_id(&self) -> &'static str;
    fn kind(&self) -> RiskKind;
    fn short_description(&self) -> &'static str;
}

// ── Rule registry ─────────────────────────────────────────────────────────────

pub struct ShiftTruncationRule;
pub struct FakeCheckedShiftRule;
pub struct InvalidShiftCountRule;
pub struct NarrowCastRule;
pub struct LossyRightShiftRule;
pub struct SuspiciousBitwiseArithmeticRule;
pub struct WeakDenominatorRule;
pub struct RoundingMismatchRule;

macro_rules! impl_rule {
    ($t:ty, $id:expr, $kind:expr, $desc:expr) => {
        impl Rule for $t {
            fn rule_id(&self) -> &'static str { $id }
            fn kind(&self) -> RiskKind { $kind }
            fn short_description(&self) -> &'static str { $desc }
        }
    };
}

impl_rule!(
    ShiftTruncationRule,
    "security/reachable-shift-truncation",
    RiskKind::ReachableShiftTruncation,
    "Left-shift discards high bits when the input exceeds the safe threshold"
);
impl_rule!(
    FakeCheckedShiftRule,
    "security/fake-checked-shift",
    RiskKind::FakeCheckedShift,
    "A custom overflow guard exists but is weaker than the true no-truncation bound"
);
impl_rule!(
    InvalidShiftCountRule,
    "security/invalid-shift-count",
    RiskKind::InvalidShiftCount,
    "Shift count is >= type width, which aborts at runtime"
);
impl_rule!(
    NarrowCastRule,
    "security/reachable-narrow-cast",
    RiskKind::ReachableNarrowCast,
    "Cast to a narrower type can abort when the value exceeds the destination max"
);
impl_rule!(
    LossyRightShiftRule,
    "security/reachable-lossy-right-shift",
    RiskKind::ReachableLossyRightShift,
    "Right-shift used as division silently discards non-zero low bits"
);
impl_rule!(
    SuspiciousBitwiseArithmeticRule,
    "security/suspicious-bitwise-arithmetic",
    RiskKind::SuspiciousBitwiseArithmetic,
    "Bitwise result whose exact range is unknown feeds downstream arithmetic"
);
impl_rule!(
    WeakDenominatorRule,
    "security/reachable-weak-denominator",
    RiskKind::ReachableWeakDenominator,
    "Denominator may be zero or its individual factors are not proven strictly positive"
);
impl_rule!(
    RoundingMismatchRule,
    "security/reachable-rounding-mismatch",
    RiskKind::ReachableRoundingMismatch,
    "Semantically related quantity reaches a sink under inconsistent rounding modes"
);

/// All rules in priority order (higher index = checked later / lower priority).
pub fn all_rules() -> Vec<Box<dyn Rule>> {
    vec![
        Box::new(InvalidShiftCountRule),
        Box::new(FakeCheckedShiftRule),
        Box::new(ShiftTruncationRule),
        Box::new(NarrowCastRule),
        Box::new(LossyRightShiftRule),
        Box::new(WeakDenominatorRule),
        Box::new(RoundingMismatchRule),
        Box::new(SuspiciousBitwiseArithmeticRule),
    ]
}
