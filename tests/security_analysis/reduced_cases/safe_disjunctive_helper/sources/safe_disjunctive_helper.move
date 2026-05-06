module reduced::safe_disjunctive_helper {
    public fun safe_checked_shlw(n: u256): (u256, bool) {
        let bound = 1u256 << 192;
        if (n == 0) {
            ((n << 64), false)
        } else if (n < bound) {
            ((n << 64), false)
        } else {
            (0, true)
        }
    }

    public fun safe_liquidity_amount(n: u256): u256 {
        let (scaled, overflow) = safe_checked_shlw(n);
        assert!(!overflow, 0);
        scaled
    }
}
