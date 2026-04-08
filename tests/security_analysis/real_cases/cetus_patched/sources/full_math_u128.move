module cetus_clmm::full_math_u128 {
    public fun full_mul(a: u128, b: u128): u256 {
        (a as u256) * (b as u256)
    }
}
