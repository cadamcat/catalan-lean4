# Third-party code and mathematical sources

## ClassFieldTheory

The `vendor/ClassFieldTheory/Lean4/` directory contains 871 unmodified Lean source files from [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/2930b56f4b5c33ddab9ef91a45a4811d6f7a683f), commit `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f`.

The upstream authors retain credit for those files. Their [Apache-2.0 license](vendor/ClassFieldTheory/LICENSE) is included. The upstream repository has no NOTICE file, and its source files carry no per-file copyright headers. [SOURCES.json](vendor/ClassFieldTheory/SOURCES.json) specifies the retained paths, hashes, byte counts, and selected entry modules. The local directory README describes the packaging; the Lean sources are unchanged.

## Mathlib and Lean

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) is used at commit `0df444a360eaa60ab8c11dca51a86af692955474` under its Apache-2.0 license. Mathlib and its transitive packages are fetched using [lake-manifest.json](lake-manifest.json), rather than redistributed in this source tree. Their original licenses and notices remain in those packages.

Lean is selected by [lean-toolchain](lean-toolchain). Its compiler and runtime are installed separately.

## Mathematical references and source acknowledgments

The mathematical theorem is due to Preda Mihăilescu. Yuri Bilu's exposition supplies the principal presentation of the cyclotomic approach followed here; bibliographic references are in the [README](README.md#mathematical-references).

The source comments in [DigitValuation.lean](Catalan/Stickelberger/DigitValuation.lean) and [ClassReduction.lean](Catalan/Stickelberger/ClassReduction.lean) acknowledge the mathematical arguments in [xroblot/SKW](https://github.com/xroblot/SKW/tree/4db8676808a63d892a8f36ead11308ca8dd58520), fixed at commit `4db8676808a63d892a8f36ead11308ca8dd58520`. These acknowledgments are retained. No SKW package or source module is imported or vendored.
