module reduced::weak_sink {
    public fun debug_shift(x: u256): u256 {
        let shifted = x << 64;
        shifted + 1
    }
}
