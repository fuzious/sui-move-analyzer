module reduced::lossy_right_shift {
    public fun liquidity_amount(x: u256): u256 {
        let shifted = x >> 1;
        shifted + 1
    }
}
