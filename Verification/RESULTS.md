# Verification snapshot

Checks completed on 2026-09-19 with Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). The checked input files and their SHA-256 digests are listed in [input-manifest.json](input-manifest.json).

| Check | Result |
| --- | --- |
| Fixed vendor inventory, file hashes, and license | 871 Lean source files matched the retained source manifest. |
| Project source build | 498 Catalan modules and 871 vendored modules compiled from source with `--trust=0`. |
| Unified axiom audit | All 1390 expected reports were present and used only the standard axioms. |
| Public theorem audit | All five public roots used only `propext`, `Classical.choice`, and `Quot.sound`. |
| Statement checks | The natural, signed-integer, and consecutive-perfect-power restatements compiled; their three axiom reports were standard. |
| Kernel replay | All 129467 dependency constants were accepted in a fresh kernel environment; all five roots were present with identical types. |
| Verification-script controls | Eight Python tests passed. Disposable replay controls, not included in this repository, accepted an unchanged theorem, rejected an ill-typed proof by name, and rejected a non-theorem root. |

Recorded outputs:

- [Public theorem types and axioms](axioms.txt)
- [Unified axiom audit](unified-axioms.txt)
- [Statement checks](statements.txt)
- [Kernel replay](replay.txt)

Mathlib and its transitive packages used the exact locked revisions and existing compiled caches. They were not all rebuilt from source. Their constants used by the target proofs were included in the kernel replay. These checks do not by themselves constitute JSP's required review of a selected Git commit; see [the verification guide](../docs/verification.md#jsp-submission-verification).
