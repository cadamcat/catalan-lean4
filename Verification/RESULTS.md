# Verification results

## Lean 4.35.0-rc3 Palomar port

Checks run on 2026-10-05 for the port released as `v1.1.0`. The clean build was timed at commit `83a9bb3`. The final Lean sources are those of commit `e0e69f2`, which only adds visibility declarations to `Challenge.lean` and `Solution.lean`; the commits after it change no Lean file. The five public Catalan theorems and the three restatements in `Verification/Statements.lean` keep their `v1.0.0` statements.

Lean is `v4.35.0-rc3` (Lake `5.0.0-src+470d5ce`). Mathlib is also `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`. Mathlib and its package dependencies were supplied by the `lake exe cache get` cache; they were not rebuilt from source.

| Check | Result |
| --- | --- |
| Clean full target build | `Catalan`, `ClassFieldTheory`, `ValuedFieldTheory`, `GaloisCohomology`, `Verification`, `Challenge`, and `Solution` passed; Lake reported 10,338 jobs. |
| Build resources | On macOS with six parallel Lean processes: wall time 1,025 s; peak memory 3.8 GiB per Lean process and 15.6 GiB in total. |
| Final all-target build | The same seven targets passed again at `e0e69f2`. |
| Vendor reconstruction | 871 retained ClassFieldTheory sources and the license reconstructed successfully from recorded upstream files plus the port patch. A copy with one byte changed in `Lean4/ClassFieldTheory/AlgebraicNumberTheory/AdeleBaseChange.lean` was rejected, and the check named that file. |
| Unified axiom audit | All 1,390 reports passed; only `propext`, `Classical.choice`, and `Quot.sound` were found. |
| Protected theorem audit | All five public Catalan results use only `propext`, `Classical.choice`, and `Quot.sound`. |
| Statement checks | The three restated natural, signed-integer, and consecutive-power statements compiled with only the permitted axioms. |
| Kernel replay | All five roots were present with identical types; the fresh kernel accepted the 131,214-constant cone with no unsafe or partial declarations and no nonstandard axioms. A cone scan found no `Lean.ofReduceBool` dependency. |
| Comparator | With the committed `comparator.json` (NanoDa enabled), the Challenge and Solution exports matched, and both the NanoDa kernel and Lean's default kernel accepted the solution ("Your solution is okay!"). Tools: Comparator `fd5d5bcf14177b187f66d4502071268d877887c3`, lean4export `v4.35.0-rc3` (`66f1fb4bc256072069767fce52d39480e4524869`), NanoDa `3a2407216ee84a75f9e1aead6803d0578be06ae7`. The run was on macOS with Comparator's development sandbox shim. |

The measured clean build used:

```sh
lake build Catalan ClassFieldTheory ValuedFieldTheory GaloisCohomology Verification Challenge Solution
```

The result files are [public theorem types and axioms](axioms.txt), [the unified axiom audit](unified-axioms.txt), [statement checks](statements.txt), and [kernel replay](replay.txt). Lean 4.35.0-rc3 emits a deprecation warning for `Lean.Environment.replay`; the fresh-kernel replay completed successfully.

## Earlier verification snapshot

These results describe the earlier proof snapshot completed on 2026-09-19 with Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). Its checked inputs and SHA-256 digests are listed in [input-manifest.json](input-manifest.json). Later checks of selected proof commit `897079dab4c8dc980cc9b98ab28fed846e4a756f`, including fresh Linux verification and a full Mathlib source rebuild, are recorded in [Supplemental/README.md](Supplemental/README.md); they remain historical evidence for that commit.

| Check | Result |
| --- | --- |
| Project source build | 498 Catalan modules and 871 vendored modules compiled from source with `--trust=0`. |
| Unified axiom audit | All 1,390 expected reports used only standard axioms. |
| Public theorem audit | All five public roots used only `propext`, `Classical.choice`, and `Quot.sound`. |
| Statement checks | The natural, signed-integer, and consecutive-perfect-power restatements compiled with standard axioms. |
| Kernel replay | All 129,467 dependency constants were accepted in a fresh kernel environment; all five roots were present with identical types. |
| Verification-script controls | Eight Python tests passed. Disposable replay controls accepted an unchanged theorem and rejected an ill-typed proof and a non-theorem root. |

Mathlib and its transitive packages used exact locked revisions and existing compiled caches in that snapshot; they were not all rebuilt from source. These checks do not certify the port. The snapshot's recorded outputs are in release `v1.0.0`; the output files in this directory now hold the port's results.
