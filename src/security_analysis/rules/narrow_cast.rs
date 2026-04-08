use crate::security_analysis::domain::uint_max;
use move_core_types::u256::U256;

pub fn cast_max(width: u16) -> U256 {
    uint_max(width)
}
