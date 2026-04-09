# sui-move-analyzer

> **Assignment submission note** — the security analysis section below documents the proof-of-concept built for the take-home. Jump straight to [Verification](#Verification) to reproduce the findings.

---

## What was built

Move's compiler and runtime already protect against arithmetic bugs: `a + b` overflows → aborts, `a / 0` → aborts, a narrowing cast that doesn't fit → aborts. Existing static analyzers extend this further and flag precision loss, rounding errors, and weak divisors for arithmetic operations.

But DeFi developers — especially in CLMM and fixed-point math codebases — routinely use bitwise ops *as* arithmetic because it's faster. `x << 64` is `x * 2^64`. `x >> 64` is `x / 2^64`. Masking with `x & 0xFFFF` is cheap range bounding. The `integer-mate` library that Cetus built on top of does this throughout, and so do most concentrated liquidity AMMs, lending rate calculators, and oracle scaling implementations on Sui. Neither the compiler nor any existing static analyzer applies overflow or precision reasoning to bitwise operations — they see bit manipulation and move on.

This project adds a post-CFGIR security pass that applies the same class of analysis existing tools apply to arithmetic, but for the bitwise equivalents. **The Cetus exploit is one instance of this family — not the only target.**

### Signals

| Signal | Rule ID | Runtime | Existing static tools | This pass |
|---|---|---|---|---|
| Shift truncation | `security/reachable-shift-truncation` | silent | silent | catches it |
| Fake checked shift | `security/fake-checked-shift` | silent | silent | catches it |
| Lossy right shift | `security/reachable-lossy-right-shift` | silent | silent | catches it |
| Suspicious bitwise arithmetic | `security/suspicious-bitwise-arithmetic` | silent | silent | catches it |
| Rounding mismatch | `security/reachable-rounding-mismatch` | silent | silent | catches it |
| Invalid shift count | `security/invalid-shift-count` | aborts (u8–u128), **silent on u256** | miss | catches both; u256 case has no other defense |
| Narrowing cast after shift | `security/reachable-narrow-cast` | aborts at runtime | miss bitwise paths | catches statically on shift/bitwise paths |
| Weak denominator (product) | `security/reachable-weak-denominator` | aborts if exactly zero | flag simple zero denom | catches product denominators where `assert!(product > 0)` exists but each factor is not independently proven `> 0` |

**On weak denominator specifically:** Runtime and existing tools handle `x / 0` (abort) and simple provably-zero denominators (flag). What they miss is `denominator = price_a * price_b` with an `assert!(denominator > 0)` guard — existing tools see the assert and consider it safe. This pass recognises that a product guard is not sufficient; each factor must be independently proven strictly positive. That is the structural CLMM vulnerability: the product is non-zero, but near-zero enough that the quotient explodes. The fix (verified in the patched fixture) is `assert!(price_a > 0); assert!(price_b > 0)` — individual factor guards, not a product guard.

### What protocols are in scope

Any Sui Move protocol that uses shift-based fixed-point arithmetic or CLMM-style price math is in scope — not just Cetus clones. Concretely:

- **CLMMs / concentrated liquidity AMMs** — the denominator and shift patterns are structural to this design, not Cetus-specific
- **Lending / interest rate math** — rate scaling via `>> n` is common; lossy right shift applies
- **Oracles / price feeds** — `price << 64` for fixed-point scaling; truncation and fake-checked-shift apply
- **Fee calculators** — `amount & fee_mask` fed into arithmetic; suspicious-bitwise-arithmetic applies
- **Any protocol using a helper library for "safe" shifts** — fake-checked-shift catches wrong-bound guards regardless of library name

### What the analyzer correctly suppresses (not noisy)

The following patterns are verified to produce **no findings**:

- `x & mask` where mask proves the value fits the cast target — suppressed via bit-fact propagation
- `x <= (1 << 192) - 1` guard before `x << 64` — suppressed via path-sensitive interval narrowing
- `assert!(x <= bound)` before shift — suppressed
- Disjunctive guards (`if a == 0 ... else if a < bound ... else abort`) — suppressed
- `denom != 0` guard before division — suppressed
- `x >> n` where bit facts prove the low `n` bits are zero — suppressed

### How it works

- Runs on the compiler's own CFGIR output — typed IR, not text regex
- Interval + bit-fact abstract interpretation: every variable carries `[lower, upper]` + `known_zero`/`known_one` bitmasks
- Path-sensitive: facts are narrowed through `if`/`assert!` branches, so guarded code is suppressed
- Interprocedural: function summaries carry risk origins across helper call chains, so a bug inside a library surfaces at the call site
- Sink-based: findings only fire when a risky value reaches a public return, a financial call argument, a struct field write, or downstream arithmetic — not on every shift in the codebase
- Severity is graded: financial sinks produce `NonblockingError`, non-financial context produces `Warning`

---

## Verification

**Prerequisites:** Rust toolchain, `sui` CLI on PATH (needed for the Cetus CLMM package build step), internet access to clone pinned repos.

### Step 1 — unit tests (local fixtures, no network)

```bash
cargo test security
```
![alt text](<Screenshot from 2026-04-09 11-03-37.png>)
This runs the full fixture suite. Key cases:

| Fixture | Signal expected | Notes |
|---|---|---|
| `real_cases/cetus_vulnerable` | `fake-checked-shift` | The actual Cetus bug pattern |
| `real_cases/cetus_patched` | clean on `fake-checked-shift` | Correct `>=` bound suppresses it |
| `reduced_cases/unsafe_direct` | `reachable-shift-truncation` | Unguarded `x << 64` |
| `reduced_cases/helper_and_cast` | `fake-checked-shift` + `reachable-narrow-cast` | Wrong-bound helper + downstream cast |
| `reduced_cases/lossy_right_shift` | `reachable-lossy-right-shift` | `x >> 1` with non-zero low bits |
| `reduced_cases/bitwise_warning` | `suspicious-bitwise-arithmetic` (×2) | `x \| 1` and `x ^ 0xff` before arithmetic |
| `reduced_cases/invalid_shift` | `invalid-shift-count` | Shift count equals bit width |
| `reduced_cases/weak_denominator_warning` | `reachable-weak-denominator` | Product-level guard insufficient |
| `reduced_cases/semantic_rename` | `reachable-weak-denominator` | Fires even with non-financial variable names (alpha, beta, gamma) |
| `reduced_cases/rounding_mismatch` | `reachable-rounding-mismatch` | ceil_div vs floor div in same formula |
| `reduced_cases/safe_guards` | clean | Correct bound suppressed |
| `reduced_cases/masked_cast_safe` | clean | Bit-fact proves cast fits |
| `reduced_cases/safe_right_shift` | clean | Bit-fact proves low bits zero |
| `reduced_cases/safe_disjunctive_helper` | clean | OR-guard covers full safe range |
| `sink_cases/weak_sink` | `reachable-shift-truncation` at `Warning` only | Non-financial sink → lower severity than Cetus path |
| `dependency_cases/scope_*` | scope filtering works | Root-only vs direct vs transitive |

### Step 2 — Cetus exploit family on pinned public history

This script clones three historical revisions of the actual `integer-mate` library and the pinned Cetus CLMM package, runs the analyzer on each, and asserts the expected signal transitions:

```bash
bash scripts/demo_cetus_exploit_family.sh
```

Expected output (final line on success):

```
[demo] success: analyzer distinguishes vulnerable, partially fixed, and fixed integer-mate revisions and still produces exploit-family findings on pinned Cetus CLMM
```

What the script verifies:

| Revision | Expected | Key signal |
|---|---|---|
| `integer-mate` @ `8176959` (vulnerable) | flagged | `security/fake-checked-shift` ✓ |
| `integer-mate` @ `ffb2292` (partial fix) | flagged | `security/fake-checked-shift` ✓ |
| `integer-mate` @ `970667a` (full fix) | clean on that signal | `security/fake-checked-shift` absent ✓ |
| `cetus-clmm` @ `74e98b6` | flagged | `security/reachable-weak-denominator` ✓ |

### Step 3 — corpus runner (structured table output)

```bash
cargo run --bin security_corpus -- \
  --manifest tests/security_analysis/corpus/packages.toml \
  --format table
```

This runs the same four packages with pass/fail assertions and prints a summary table. All four should show `PASS`.

### Step 4 — run against any local Move package

```bash
cargo run --bin security_demo -- \
  --dependency-mode auto \
  --scope direct \
  path/to/your/package
```

---

**Table of Contents**
* [Introduction](#Introduction)
* [Features](#Features)
* [Support](#Support)

## Introduction <span id="Introduction">
The **sui-move-analyzer** is a Visual Studio Code plugin for **Sui Move** language developed by [MoveBit](https://movebit.xyz). Although this is an alpha release, it has many useful features, such as **highlight, autocomplete, go to definition/references**, and so on.

## Features <span id="Features">

Here are some of the features of the sui-move-analyzer Visual Studio Code extension. To see them, open a
Move source file (a file with a `.move` file extension) and:

- See Move keywords and types highlighted in appropriate colors.
- As you type, Move keywords will appear as completion suggestions.
- If the opened Move source file is located within a buildable project (a `Move.toml` file can be
  found in one of its parent directories), the following advanced features will also be available:
  - compiler diagnostics
  - sui commands line tool(you need install Sui Client CLI locally)
  - sui project template
  - go to definition
  - go to references
  - type on hover
  - inlay hints
  - linter for move file
  - ...

## Support <span id="Support">

1.If you find any issues, please report a GitHub issue to the [issue](https://github.com/movebit/sui-move-analyzer/issues) repository to get help.

2.Welcome to the developer discussion group as well: [MoveAnalyzer](https://t.me/moveanalyzer). 
