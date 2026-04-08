module local_math::helper {
    public fun checked_shlw(n: u256): u256 {
        assert!(n <= 18446744073709551615u256, 0);
        n << 64
    }
}
