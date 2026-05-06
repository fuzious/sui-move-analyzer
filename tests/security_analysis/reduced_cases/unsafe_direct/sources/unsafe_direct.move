module reduced::unsafe_direct {
    public fun unsafe_amount(x: u256): u256 {
        x << 64
    }
}
