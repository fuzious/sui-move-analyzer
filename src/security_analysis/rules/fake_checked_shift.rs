use move_core_types::u256::U256;

pub fn guard_is_weaker_than_threshold(guard_upper_bound: Option<U256>, threshold: U256) -> bool {
    match guard_upper_bound {
        Some(bound) => bound > threshold,
        None => false,
    }
}
