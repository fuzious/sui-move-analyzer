module cetus_clmm::clmm_math {
    use cetus_clmm::full_math_u128;
    use integer_mate::math_u256;

    const EMULTIPLICATION_OVERFLOW: u64 = 1;
    const EAMOUNT_CAST_TO_U64_OVERFLOW: u64 = 2;

    public fun get_delta_a(
        sqrt_price_0: u128,
        sqrt_price_1: u128,
        liquidity: u128,
        round_up: bool,
    ): u64 {
        let sqrt_price_diff = if (sqrt_price_0 > sqrt_price_1) {
            sqrt_price_0 - sqrt_price_1
        } else {
            sqrt_price_1 - sqrt_price_0
        };
        if (sqrt_price_diff == 0 || liquidity == 0) {
            return 0
        };

        let (numberator, overflowing) = math_u256::checked_shlw(
            full_math_u128::full_mul(liquidity, sqrt_price_diff),
        );
        if (overflowing) {
            abort EMULTIPLICATION_OVERFLOW
        };

        let denominator = full_math_u128::full_mul(sqrt_price_0, sqrt_price_1);
        let quotient = math_u256::div_round(numberator, denominator, round_up);
        assert!(quotient <= 0xffffffffffffffffu256, EAMOUNT_CAST_TO_U64_OVERFLOW);
        (quotient as u64)
    }

    public fun quote_liquidity_amount_a(
        sqrt_price_0: u128,
        sqrt_price_1: u128,
        liquidity: u128,
    ): u64 {
        get_delta_a(sqrt_price_0, sqrt_price_1, liquidity, true)
    }
}
