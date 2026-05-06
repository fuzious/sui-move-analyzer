module reduced::helper_and_cast {
    public fun checked_shlw(n: u256): (u256, bool) {
        let bound = 1u256 << 193;
        if (n >= bound) {
            (0, true)
        } else {
            ((n << 64), false)
        }
    }

    public fun liquidity_amount_from_helper(n: u256): u256 {
        let (scaled, overflow) = checked_shlw(n);
        assert!(!overflow, 0);
        scaled
    }

    public fun cast_price_amount(x: u256): u128 {
        let shifted = x << 64;
        (shifted as u128)
    }
}
