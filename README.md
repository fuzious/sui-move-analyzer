# sui-move-analyzer

> **Assignment submission note**  
> I wrote the security analysis section below for the take-home assignment. If you want to reproduce the results, go straight to [Verification](#verification).

---

## What I built

![Architecture](achitecture_bitwise.png)

Move's compiler and runtime already catch a lot of arithmetic bugs. If `a + b` overflows, it aborts. If `a / 0` happens, it aborts. If a narrowing cast does not fit, it aborts. Existing static analyzers go further and flag things like precision loss, rounding errors, and weak divisors in arithmetic code.

In DeFi code, especially in CLMM and fixed-point math, developers often use bitwise operations like arithmetic because they are faster. For example:

- `x << 64` means `x * 2^64`
- `x >> 64` means `x / 2^64`
- `x & 0xFFFF` is often used to keep a value in range

The `integer-mate` library used by Cetus does this a lot. So do many concentrated liquidity AMMs, lending rate calculators, and oracle scaling implementations on Sui. The problem is that the compiler and existing analyzers usually treat these as plain bit manipulation. They do not apply overflow or precision checks to them.

I built a post-CFGIR security pass to close that gap. It applies the same kind of reasoning people already use for arithmetic, but on bitwise equivalents instead. The Cetus exploit is one example of this bug family. It is not the only one.

### Signals

| Signal | Rule ID | Runtime | Existing static tools | This pass |
|---|---|---|---|---|
| Shift truncation | `security/reachable-shift-truncation` | silent | silent | catches it |
| Fake checked shift | `security/fake-checked-shift` | silent | silent | catches it |
| Lossy right shift | `security/reachable-lossy-right-shift` | silent | silent | catches it |
| Suspicious bitwise arithmetic | `security/suspicious-bitwise-arithmetic` | silent | silent | catches it |
| Rounding mismatch | `security/reachable-rounding-mismatch` | silent | silent | catches it |
| Invalid shift count | `security/invalid-shift-count` | aborts for `u8` to `u128`, silent on `u256` | missed | catches both, and the `u256` case has no other defense |
| Narrowing cast after shift | `security/reachable-narrow-cast` | aborts at runtime | misses bitwise paths | catches it statically on shift and bitwise paths |
| Weak denominator (product) | `security/reachable-weak-denominator` | aborts only if the denominator is exactly zero | flags simple zero denominators | catches product denominators where `assert!(product > 0)` exists but each factor is not independently proven to be greater than zero |

---

## Verification

Prerequisites: `git`, Rust toolchain (`cargo`). The script also requires the `sui` CLI to pre-fetch Sui framework dependencies for the real Cetus package; the vendored commands below do not.

**With the `sui` CLI (runs against real on-chain code):**

```
bash scripts/demo_cetus_exploit_family.sh
```

Clones the real Cetus CLMM repo (commit `74e98b6`) and the real integer-mate repo at three pinned revisions (vulnerable → partial fix → fully fixed), runs the analyzer on each, and asserts the correct findings appear and disappear at each stage.

**Without the `sui` CLI (vendored fixtures, no network needed):**

```
cargo test --lib security_analysis
```

31 tests, all vendored. Each test name maps to a specific claim and includes enforced negative cases (patched versions must produce zero findings for their specific rule).

```
cargo run --bin security_demo -- tests/security_analysis/real_cases/cetus_vulnerable
```

Expected output includes `math_u256.move | 7 | ... | NonblockingError | security/fake-checked-shift` — the exact helper, line, and rule that caused the $223M loss.
