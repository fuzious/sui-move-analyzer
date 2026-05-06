module reduced::full_math_u128 {
    public fun full_mul(a: u128, b: u128): u256 {
        (a as u256) * (b as u256)
    }
}

module reduced::math_u256 {
    public fun div_round(num: u256, denom: u256, round_up: bool): u256 {
        let p = num / denom;
        if (round_up && ((p * denom) != num)) {
            p + 1
        } else {
            p
        }
    }
}

module reduced::weak_denominator_warning {
    use reduced::full_math_u128;
    use reduced::math_u256;

    public fun quote_amount(
        sqrt_price_0: u128,
        sqrt_price_1: u128,
        liquidity: u128,
    ): u64 {
        let sqrt_price_diff = if (sqrt_price_0 > sqrt_price_1) {
            sqrt_price_0 - sqrt_price_1
        } else {
            sqrt_price_1 - sqrt_price_0
        };
        let numerator = full_math_u128::full_mul(liquidity, sqrt_price_diff);
        let denominator = full_math_u128::full_mul(sqrt_price_0, sqrt_price_1);
        assert!(denominator > 0, 0);
        let quotient = math_u256::div_round(numerator, denominator, true);
        (quotient as u64)
    }
}
