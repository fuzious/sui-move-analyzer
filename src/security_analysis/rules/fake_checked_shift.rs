use move_core_types::u256::U256;

/// Returns `true` when `guard_upper_bound` is present but strictly exceeds
/// `threshold` — meaning the guard lets through values that *will* truncate.
///
/// A guard of `None` means no guard exists at all (different from a weak one).
/// Callers should check `has_guard && guard_is_weaker_than_threshold(...)` to
/// distinguish the two cases before choosing `FakeCheckedShift` vs
/// `ReachableShiftTruncation`.
pub fn guard_is_weaker_than_threshold(guard_upper_bound: Option<U256>, threshold: U256) -> bool {
    match guard_upper_bound {
        Some(bound) => bound > threshold,
        None => false,
    }
}
