module reduced::invalid_shift {
    public fun bad_shift_count(x: u64): u64 {
        x << 64
    }
}
