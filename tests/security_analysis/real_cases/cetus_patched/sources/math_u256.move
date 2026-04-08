module integer_mate::math_u256 {
    public fun checked_shlw(n: u256): (u256, bool) {
        let bound = 1u256 << 192;
        if (n >= bound) {
            (0, true)
        } else {
            ((n << 64), false)
        }
    }

    public fun div_round(num: u256, denom: u256, round_up: bool): u256 {
        let p = num / denom;
        if (round_up && ((p * denom) != num)) {
            p + 1
        } else {
            p
        }
    }
}
