module reduced::dynamic_u256_shift {
    public fun amount_from_dynamic_shift(x: u256, y: u8): u256 {
        x << y
    }
}
