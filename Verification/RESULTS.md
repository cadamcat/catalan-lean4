# Verification results

## Lean 4.35.0-rc3 Palomar port

Checks run on 2026-10-05 for the `palomar` branch. The final source targets are recorded at commit `e0e69f2`; the measured clean build at `83a9bb3` covered all seven requested Lake targets before a visibility-only update to `Challenge.lean` and `Solution.lean`. After that update, the complete target command and Comparator passed again. The protected Catalan declarations and the three `Verification/Statements.lean` restatements were unchanged; the file has the required module-system header and visibility prefix.

Lean is `v4.35.0-rc3` (Lake `5.0.0-src+470d5ce`). Mathlib is also `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`. Mathlib and its package dependencies were supplied by the `lake exe cache get` cache; they were not rebuilt from source.

| Check | Result |
| --- | --- |
| Clean full target build | `Catalan`, `ClassFieldTheory`, `ValuedFieldTheory`, `GaloisCohomology`, `Verification`, `Challenge`, and `Solution` passed; Lake reported 10,338 jobs. |
| Build resources | Wall time 1,024.56 s; `N=6`; six maximum concurrent Lean processes; peak Lean RSS 3.777 GiB per process; `N × peak` 22.662 GiB; peak aggregate Lean RSS 15.608 GiB. `/usr/bin/time -l` reported a maximum resident set size of 4,058,873,856 bytes. |
| Final all-target build | The same seven targets passed after the public/expose sections were added to the Palomar modules. |
| Vendor reconstruction | 871 retained ClassFieldTheory sources and the license reconstructed successfully from recorded upstream files plus the port patch. The disposable one-byte mutation control failed while naming `Lean4/ClassFieldTheory/AlgebraicNumberTheory/AdeleBaseChange.lean`. |
| Unified axiom audit | All 1,390 reports passed; only `propext`, `Classical.choice`, and `Quot.sound` were found. |
| Protected theorem audit | All five public Catalan results use only `propext`, `Classical.choice`, and `Quot.sound`. |
| Statement checks | The three restated natural, signed-integer, and consecutive-power statements compiled with only the permitted axioms. |
| Kernel replay | All five roots were present with identical types; the fresh kernel accepted the 131,214-constant cone with no unsafe or partial declarations and no nonstandard axioms. A cone scan found no `Lean.ofReduceBool` dependency. |
| Comparator | With a temporary config using the built-in Lean kernel, Challenge and Solution exports matched and the kernel accepted the solution. The NanoDa-enabled run status is recorded separately in `REPORT.md`. |

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

Mathlib and its transitive packages used exact locked revisions and existing compiled caches in that snapshot; they were not all rebuilt from source. These checks do not certify the Palomar port.
