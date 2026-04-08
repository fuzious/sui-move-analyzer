module root::entry {
    use local_math::helper;

    public fun quote(seed: u256): u256 {
        helper::checked_shlw(seed)
    }
}
