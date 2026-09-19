# Reproducing the verification

Run commands from the repository root with the toolchain in `lean-toolchain`. Dependency revisions are locked in `lake-manifest.json`; do not run `lake update` when checking a fixed source version.

## Source build and axiom checks

```sh
lake exe cache get
./scripts/verify.sh
```

The script verifies the fixed vendor file inventory and hashes, builds `Catalan.Audit`, checks the public theorem statements, and runs the axiom-log parser against the expected declarations in the audit source files. A missing report, an unparsed report, a Lean error, or an axiom outside `propext`, `Classical.choice`, and `Quot.sound` causes failure. Names containing apostrophes and lists wrapping across lines are supported.

Building `Catalan.Audit` explicitly includes its audit-only vendor imports. A plain `lake build` need not build that module. The script therefore does not rely on pre-existing class-field-theory build artifacts.

Outputs are written to `verification-results/`, which is not tracked. The command exits nonzero if any build, source check, or axiom check fails. The parser's regression tests can be run separately:

```sh
python3 -m unittest discover -s scripts/tests -v
```

## Kernel replay

```sh
./scripts/replay.sh
```

[Verification/Replay.lean](../Verification/Replay.lean) loads the five public roots, traverses their types and proof bodies, and submits the complete dependency cone to a new, empty Lean kernel environment. It rejects missing declarations, unsafe or partial declarations in the cone, nonstandard axioms, absent roots, and changed root types. This uses the same fixed Lean kernel in a separate replay; it is not a claim of verification by a different proof assistant.

## Scope of a clean run

For a project-source rebuild, start from a fresh copy with no project `.lake/build` directory. `lake exe cache get` uses precompiled Mathlib dependencies. Such a run rebuilds the Catalan and vendored sources but is not a from-source rebuild of every upstream package. Kernel replay checks the dependency constants used by the target theorems, including constants loaded from those caches.

`--no-cache` alone does not remove incremental build artifacts. Module `.olean` files can include source paths in diagnostic messages, so cross-directory byte equality is not a general reproducibility criterion. Check the source version, theorem statements, build results, and axiom/replay outputs.

## JSP submission verification

JSP's [submission requirements](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/CONTRIBUTING.md#external-solver-and-lean-submissions) require the bundled `lean-verify` process to report Verification passed for the exact proof commit selected for submission. The repository's build and audit scripts provide reproducible evidence, but do not replace that required review. Run it after selecting the published commit, and repeat it if that commit changes.
