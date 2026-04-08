module reduced::masked_cast_safe {
    public fun amount_from_mask(x: u256): u128 {
        let masked = x & 0xffffffffffffffffffffffffffffffffu256;
        (masked as u128)
    }
}
