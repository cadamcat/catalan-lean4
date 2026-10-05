# Third-party code and mathematical sources

## ClassFieldTheory

The `vendor/ClassFieldTheory/Lean4/` directory contains 871 Lean source files selected from [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/2930b56f4b5c33ddab9ef91a45a4811d6f7a683f), commit `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f`.

The upstream authors retain credit for those files. Their [Apache-2.0 license](vendor/ClassFieldTheory/LICENSE) is included. The upstream repository has no NOTICE file, and its source files carry no per-file copyright headers.

## Modifications

The retained files use the Lean module system and the visibility declarations required by Lean `v4.35.0-rc3`. They were ported from upstream ClassFieldTheory commit `7713795234690681b4406ae198b07aa95e82716a`, which targets Lean `v4.35.0-rc2`, and updated for Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`. Each changed Lean file has a notice before its `module` header naming the port commit and the kind of change.

[SOURCES.json](vendor/ClassFieldTheory/SOURCES.json) records each file's original upstream commit and path, port commit and path, and reconstruction patch. The patch applies to the original vendored snapshot at project commit `c08bf727e7e0f773edd2f4777fd0d12152f44ed6`; its file hashes are checked against the recorded upstream source before reconstruction. [check_vendor.py](scripts/check_vendor.py) applies that patch and compares the reconstructed bytes with the retained files. The local directory README describes the package layout.

The fixed subset does not include every support module added or split out by the upstream port. To retain its 871 paths, the required fractional-ideal norm/factorization declarations, finite-place unramified normalization, and two principal-unit quotient helpers are merged into retained modules. The multiplicative induced-function module from the separate `ProCGroups` subtree is also inlined into the retained Herbrand module, so the Lake project has no fourth vendor library. These merges are recorded in the affected files' notices and the reconstruction patch.

## Mathlib and Lean

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/c55e6e786f49471c72fbddbec5415808896aec1e) is used at commit `c55e6e786f49471c72fbddbec5415808896aec1e` under its Apache-2.0 license. Mathlib and its transitive packages are fetched using [lake-manifest.json](lake-manifest.json), rather than redistributed in this source tree. Their original licenses and notices remain in those packages.

Lean is selected by [lean-toolchain](lean-toolchain). Its compiler and runtime are installed separately.

## Mathematical references and source acknowledgments

The mathematical theorem is due to Preda Mihăilescu. Yuri Bilu's exposition supplies the principal presentation of the cyclotomic approach followed here; bibliographic references are in the [README](README.md#mathematical-references).

The source comments in [DigitValuation.lean](Catalan/Stickelberger/DigitValuation.lean) and [ClassReduction.lean](Catalan/Stickelberger/ClassReduction.lean) acknowledge the mathematical arguments in [xroblot/SKW](https://github.com/xroblot/SKW/tree/4db8676808a63d892a8f36ead11308ca8dd58520), fixed at commit `4db8676808a63d892a8f36ead11308ca8dd58520`. These acknowledgments are retained. No SKW package or source module is imported or vendored.
