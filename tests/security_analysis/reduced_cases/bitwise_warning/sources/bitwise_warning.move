module reduced::bitwise_warning {
    public fun amount_from_or(x: u256): u256 {
        let mixed = x | 1u256;
        mixed + 1
    }

    public fun amount_from_xor(x: u256): u256 {
        let mixed = x ^ 0xffu256;
        mixed + 1
    }
}
