module reduced::safe_right_shift {
    public fun exact_liquidity_amount(x: u256): u256 {
        let even_mask = (((1u256 << 255) - 1) << 1);
        let even = x & even_mask;
        even >> 1
    }
}
