module reduced::math_u128 {
    const DIV_BY_ZERO: u64 = 1;

    public fun checked_div_round(num: u128, denom: u128, round_up: bool): u128 {
        if (denom == 0) {
            abort DIV_BY_ZERO
        };
        let quotient = num / denom;
        let remainder = num % denom;
        if (round_up && (remainder > 0)) {
            quotient + 1
        } else {
            quotient
        }
    }
}

module reduced::neq_denominator_guard {
    use reduced::math_u128;

    public fun quote(num: u128, denom: u128): u128 {
        if (denom == 0) {
            return 0
        };
        math_u128::checked_div_round(num, denom, true)
    }
}
