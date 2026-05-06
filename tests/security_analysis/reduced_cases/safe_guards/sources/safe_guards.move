module reduced::safe_guards {
    public fun safe_exact_bound(x: u256): u256 {
        if (x <= ((1u256 << 192) - 1)) {
            x << 64
        } else {
            0
        }
    }

    public fun assert_narrowed(x: u256): u256 {
        assert!(x <= ((1u256 << 192) - 1), 0);
        x << 64
    }
}
