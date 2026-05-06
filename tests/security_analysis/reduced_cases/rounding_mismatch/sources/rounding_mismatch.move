module reduced::rounding_math {
    public fun ceil_div(n: u256, d: u256): u256 {
        let p = n / d;
        if ((p * d) < n) {
            p + 1
        } else {
            p
        }
    }
}

module reduced::rounding_mismatch {
    use reduced::rounding_math;

    public fun quote_mixed(flag: bool, amount: u128, scale: u128): u64 {
        assert!(scale > 0, 0);
        let numer = (amount as u256) * (scale as u256);
        let denom = (scale as u256);
        let q = if (flag) {
            rounding_math::ceil_div(numer, denom)
        } else {
            numer / denom
        };
        (q as u64)
    }
}
