[English](README.md) | [简体中文](README_zh.md)

# catalan-lean4

A Lean 4 formalization of Catalan's conjecture (Mihăilescu's theorem).

The only consecutive positive integers that are both proper perfect powers are **8 and 9**. The repository proves this statement and classifies the corresponding power equations, including nonzero integer bases of either sign.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authorship and attribution](AUTHORS.md).
- **Mathematical result:** Preda Mihăilescu’s proof of Catalan’s conjecture.
- Developed with AI assistance (Codex and Claude Code); all proofs are verified by the Lean 4 kernel.

## Main results

| Theorem | Statement |
| --- | --- |
| `Catalan.JSP.statement` | 8 and 9 are proper perfect powers; if positive `n` and `n + 1` are both proper perfect powers, then `n = 8`. |
| `Catalan.catalans_conjecture` | For natural `a, b > 1` and positive natural `x, y`, `x^a - y^b = 1` implies `a = 2`, `b = 3`, `x = 3`, `y = 2`. Subtraction is natural-number subtraction. |
| `Catalan.catalan_int` | The same classification for integer bases `x, y > 1` and the equation `x^a = y^b + 1`. |
| `Catalan.catalan_int_signed` | For nonzero integers `x, y` and natural `p, q ≥ 2`, `x^p - y^q = 1` (integer subtraction) implies `p = 2`, `q = 3`, `x = 3 ∨ x = -3`, `y = 2`. |
| `Catalan.mihailescu_odd_primes` | `x^p = y^q + 1` has no solution with nonzero integer bases and two odd prime exponents. |

The statements and proofs are in [JSP.lean](Catalan/JSP.lean), [Final/Assembly.lean](Catalan/Final/Assembly.lean), and [Final/Signed.lean](Catalan/Final/Signed.lean). They are available through `import Catalan`. The definition of a proper perfect power is explicit in `Catalan.JSP.IsProperPerfectPower`: both the natural base and exponent are at least 2.

Google DeepMind's Formal Conjectures states `Catalan.catalans_conjecture` with the same statement and links this proof as its formal proof ([Catalan.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Catalan.lean), [PR #6452](https://github.com/google-deepmind/formal-conjectures/pull/6452)).

Release `v1.1.1` is registered in the Palomar Registry as [PALOMAR-2026-10-06-000009](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-06-000009&version=1). Palomar rebuilt that commit and checked the four theorems of [Challenge.lean](Challenge.lean) with Comparator.

## Build and verify

Requirements: Git, Python 3.9 or newer, and [elan](https://github.com/leanprover/elan), with `lake` available on `PATH`. Run from the repository root:

```sh
lake exe cache get
./scripts/verify.sh
```

The first command fetches the fixed Mathlib dependencies and their compiled cache. The verification script checks the vendored sources, builds `Catalan.Audit` and its complete import closure, checks the public statements, and parses every expected axiom report. Building the audit module explicitly also builds its additional class-field-theory imports. All proof compilation uses `--trust=0`.

To recheck the full dependency cone of the five public theorems in a fresh Lean kernel environment:

```sh
./scripts/replay.sh
```

See [verification details](docs/verification.md) for commands, output locations, and the distinction between dependency caches, source builds, and kernel replay. The final theorems use only `propext`, `Classical.choice`, and `Quot.sound`; no additional axiom or missing proof is assumed.

Recorded source fingerprints and verification outputs are available in the [verification snapshot](Verification/RESULTS.md). Supplemental checks of the same submitted proof commit, including fresh Linux verification and a full Mathlib library source rebuild, are recorded in the [supplemental evidence](Verification/Supplemental/README.md).

## Fixed dependencies

- Lean `v4.35.0-rc3`, selected by [lean-toolchain](lean-toolchain).
- Mathlib `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`, fixed by [lake-manifest.json](lake-manifest.json). The project toolchain matches Mathlib's toolchain exactly.
- All regular Lean source files use Lean's module system, including the 871 retained ClassFieldTheory files.
- The ClassFieldTheory subset is based on upstream commit `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f` and carries recorded Lean 4.35 and Mathlib compatibility edits. See [third-party notices](THIRD_PARTY.md) and the [vendor README](vendor/ClassFieldTheory/README.md).

The fixed ClassFieldTheory library uses a bounded heartbeat setting in [lakefile.toml](lakefile.toml). The project does not update these sources automatically. Release `v1.1.0` ports the original release `v1.0.0` (`4bf1f74`) to Lean `v4.35.0-rc3` and the module system for the Palomar Registry; the theorem statements are unchanged.

## Mathematical references

- Preda Mihăilescu, [Primary cyclotomic units and a proof of Catalan's conjecture](https://doi.org/10.1515/crll.2004.048), *Journal für die reine und angewandte Mathematik* 572 (2004), 167–195.
- Yuri F. Bilu, [Catalan without logarithmic forms (after Bugeaud, Hanrot and Mihăilescu)](https://doi.org/10.5802/jtnb.478), *Journal de théorie des nombres de Bordeaux* 17 (2005), 69–85.

See [the statement and proof guide](docs/mathematics.md) for the public entry points and their relation to JSP-000035.

## License

Apache-2.0; see [LICENSE](LICENSE), [NOTICE](NOTICE), and [third-party attribution](THIRD_PARTY.md).
