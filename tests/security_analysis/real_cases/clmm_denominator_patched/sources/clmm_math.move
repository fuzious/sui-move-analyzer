module cetus_clmm::clmm_math {
    use cetus_clmm::full_math_u128;
    use integer_mate::math_u256;

    const EINVALID_SQRT_PRICE: u64 = 1;

    public fun quote_liquidity_amount_a(
        sqrt_price_0: u128,
        sqrt_price_1: u128,
        liquidity: u128,
    ): u64 {
        assert!(sqrt_price_0 > 0, EINVALID_SQRT_PRICE);
        assert!(sqrt_price_1 > 0, EINVALID_SQRT_PRICE);
        let sqrt_price_diff = if (sqrt_price_0 > sqrt_price_1) {
            sqrt_price_0 - sqrt_price_1
        } else {
            sqrt_price_1 - sqrt_price_0
        };
        let numerator = full_math_u128::full_mul(liquidity, sqrt_price_diff);
        let denominator = full_math_u128::full_mul(sqrt_price_0, sqrt_price_1);
        let quotient = math_u256::div_round(numerator, denominator, true);
        (quotient as u64)
    }
}
