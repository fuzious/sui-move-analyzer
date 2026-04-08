use crate::security_analysis::domain::uint_max;
use move_core_types::u256::U256;

pub fn no_truncation_threshold(width: u16, shift: u8) -> U256 {
    uint_max(width) >> shift
}
