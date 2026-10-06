# Reproducing the verification

Run commands from the repository root with Lean `v4.35.0-rc3`, selected by `lean-toolchain`. Mathlib is also at `v4.35.0-rc3` (commit `c55e6e786f49471c72fbddbec5415808896aec1e`); dependency revisions are locked in `lake-manifest.json`. Do not run `lake update` when checking a fixed source version.

## Source build and axiom checks

```sh
lake exe cache get
./scripts/verify.sh
```

The script verifies the fixed vendor file inventory by reconstructing the retained files from their recorded upstream sources and patch, builds `Catalan.Audit`, checks the public theorem statements, and runs the axiom-log parser against the expected declarations in the audit source files. A missing report, an unparsed report, a Lean error, or an axiom outside `propext`, `Classical.choice`, and `Quot.sound` causes failure. Names containing apostrophes and lists wrapping across lines are supported.

Building `Catalan.Audit` explicitly includes its audit-only vendor imports. A plain `lake build` need not build that module. The script therefore does not rely on pre-existing class-field-theory build artifacts.

## Palomar port targets

The Palomar `Challenge.lean` imports Mathlib only. `Solution.lean` imports the project and restates the four challenge declarations without importing `Challenge`. The Lake targets are `Challenge` and `Solution`. Build the complete project target set with:

```sh
lake build Catalan ClassFieldTheory ValuedFieldTheory GaloisCohomology Verification Challenge Solution
```

The current toolchain, Mathlib revision, source build measurements, four challenge comparisons, and kernel replay result are recorded in [Verification/RESULTS.md](../Verification/RESULTS.md). That record distinguishes the 2026-10-05 port checks from the historical Lean 4.33.1 snapshot and its supplemental evidence.

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

JSP's [current verification guidance](https://github.com/TheJustinSunPrize/awards/blob/66ae4831b84793bbfaed3ebd4094cacb0faafbcf/docs/verification.md#recommended-lean-pre-submission-check) recommends the `lean-verify` skill but permits other methods; self-check declarations, reports, and log links are optional. Maintainers independently review statement correspondence and reproduce proof verification before acceptance. This supersedes the mandatory-self-check wording in the earlier rule version cited by the original repository snapshot.

The proof selected in [PR #1948](https://github.com/TheJustinSunPrize/awards/pull/1948) remains commit `897079dab4c8dc980cc9b98ab28fed846e4a756f`. [Supplemental reports and logs](../Verification/Supplemental/README.md) record stricter Linux checks and a full Mathlib library source rebuild of that commit. They were added in a later evidence-only commit and do not certify a new proof version.

The official guidance explicitly allows proof commit A to be documented by a later evidence commit B without rechecking A while A remains the selected proof version. Link evidence at its own immutable commit and identify the proof commit it describes. If a different proof commit is selected, verify that version before presenting it as checked.
