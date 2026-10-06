# Supplemental verification of the submitted proof

These records concern proof commit **[`897079dab4c8dc980cc9b98ab28fed846e4a756f`](https://github.com/cadamcat/catalan-lean4/tree/897079dab4c8dc980cc9b98ab28fed846e4a756f)**. Both runs took place on 19 September 2026; the records were packaged for publication on 20 September. This evidence update records those follow-up runs against the selected proof commit; it selects no new proof version.

| Run | Environment and upstream inputs | Result |
|---|---|---|
| [Strict Linux follow-up](strict/evidence/final-summary.json) | Fresh Google Cloud Linux VM, AMD EPYC 9B45; fixed upstream dependency caches prepared separately | Five core-only targets accepted by Lean and nanoda; project audits and fresh-environment replay passed |
| [Full dependency-source build](source/evidence/final-summary.json) | Another fresh Google Cloud Linux VM, AMD EPYC 9B45; complete fixed Mathlib library and required upstream modules built without Lean package caches | The same five targets accepted by both checkers; audits and fresh-environment replay passed again |

Both runs used Lean 4.33.1 and the dependencies locked by the selected proof commit. The targets are consecutive proper perfect powers, natural solutions, positive integer solutions, nonzero signed integer solutions, and odd-prime impossibility. Their [core-only statements](common/audit/StrictChallenge.lean), [proof adapters](common/audit/StrictSolution.lean), and [comparator configuration](common/audit/config.json) are supplied. The challenge's five `sorry` bodies are specification placeholders; the solution does not import the challenge. Negative-control fixtures are also separate from the proof library.

## Strict Linux follow-up

The submitted project's first build occurred inside comparator under the recorded `systemd-run` restriction `RestrictAddressFamilies=~AF_UNIX`. A separate probe checked that AF_UNIX socket creation failed under that restriction. The setup also installed verifier-user outbound firewall rules, but the recorded socket and curl probes are not a comprehensive network-isolation audit.

- [First-build record](strict/evidence/first-submitted-execution.json), [exact command](strict/evidence/comparator-argv.json), [observed service properties](strict/evidence/comparator-unit-properties.txt), and [socket-probe result](strict/evidence/socket-probes-result.json).
- [Comparator terminal result](strict/comparator-result.txt) and [complete original log](strict/logs/comparator.log.gz).
- [Public theorem types and axioms](strict/evidence/published-axioms.txt), [statement checks](strict/evidence/published-statements.txt), and [replay output](strict/evidence/published-replay.txt). All **129,467** dependency constants were rechecked in an empty Lean kernel environment; the five roots retained their types.
- [Positive and negative controls](strict/evidence/comparator-controls.json): the valid fixture passed; a mismatched statement and an extra axiom were rejected. Corresponding logs are [positive](strict/logs/control-positive.log), [wrong statement](strict/logs/control-wrong-statement.log), and [extra axiom](strict/logs/control-extra-axiom.log).
- [Dependency identities](strict/evidence/dependency-identities.json), [trusted inputs before](strict/evidence/trusted-inputs-before.json), [after](strict/evidence/trusted-inputs-after.json), and [permission probe](strict/logs/trusted-input-permissions.log).
- [Project verification log](strict/results/verify.log.gz) and [submitter-run JSP audit-helper result](strict/results/official-audit/result.json).

## Full dependency-source build

The [pre-build identities](source/evidence/source-identities-before.json) record no prebuilt library `.olean` files in the submitted project or pinned packages. Lake configuration artifacts are separate. ProofWidgets' frontend was built from its fixed sources. The [preparation record](source/evidence/preparation.json) and archived execution scripts describe the setup.

The [coverage check](source/evidence/build-coverage.json) found **10,061 distinct successfully compiled sources**, all with `--trust=0` and package-cache retrieval disabled:

| Sources | Count |
|---|---:|
| Complete Mathlib library | 8,312 |
| Required modules from other upstream packages | 378 |
| Original Catalan modules | 498 |
| Vendored modules | 871 |
| Additional audit modules | 2 |

The raw records label the last three groups as 500 Catalan-library sources, including the two injected audit modules, plus 871 vendor sources. They do not claim to compile every unused source in every dependency. The pinned Cli checkout had no required library compilation; Mathlib's separate test, Archive, and Counterexamples libraries were outside this build.

- [Mathlib command and exit](source/evidence/mathlib-result.json) and [complete log](source/logs/mathlib.log.gz).
- [Comparator command and exit](source/evidence/comparator-result.json), [terminal result](source/comparator-result.txt), and [complete log](source/logs/comparator.log.gz).
- [Project verification log](source/logs/verify.log.gz), [public axioms](source/results/project-verification/top-level.log), [statement checks](source/results/project-verification/statements.log), [submitter-run JSP audit-helper result](source/results/official-audit/result.json), and [kernel replay log](source/logs/replay.log). The replay again accepted **129,467** dependency constants and all five root types.
- [Per-source compilation inventory](source/evidence/compiled-source-inventory.json.gz), [all 10,087 invocation records](source/compiler-invocations.tar.gz), and [record hashes](source/compiler-record-manifest.json.gz). The extra records include metadata/configuration calls and are not counted as proof-source compilations.
- [Source fingerprints before execution](source/evidence/source-fingerprints-before.json.gz), [unchanged-input result](source/evidence/source-integrity-after.json), and [dependency identities afterward](source/evidence/dependency-identities-after.json).
- [Coverage-checker controls](source/evidence/coverage-checker-controls.json) rejected missing compilation evidence, nonzero trust, and enabled caches in separate local fixtures. The strict run's comparator negative controls were **not rerun** in this source-build run.

The recorder and launchers needed compatibility fixes for the comparator sandbox. The original Lean and Lake executables were retained; the wrappers supplied cache settings and recorded compiler arguments. A preliminary comparator attempt stopped on a read-only metadata query after compiling only the auditor's challenge. The [failed-attempt log](source/logs/comparator.log.readonly-attempt), [fix record](source/evidence/logger-readonly-fix.json), wrapper revisions, and [successful continuation](source/tools/run-after-mathlib.py) are retained. The successful attempt began before any original Catalan/vendor source was compiled. These harness fixes did not change the mathematical sources or pinned dependencies.

## Trust boundary and use of the evidence

The official Lean compiler and bundled standard libraries, operating system, and checker implementations remain trusted. The target proofs use only `propext`, `Classical.choice`, and `Quot.sound`. Fresh-environment replay uses Lean's own kernel; the nanoda check is the separate kernel implementation. These are submitter-provided results, not maintainer acceptance or an independent human-review attestation.

Use [REPRODUCE.md](REPRODUCE.md) for proof reproduction, tool pins, recorded-command navigation, and archive integrity checks. The earlier cache-based run is summarized under "Earlier verification snapshot" in [RESULTS.md](../RESULTS.md); its recorded outputs are in release `v1.0.0`.

Large logs are losslessly compressed and retain their original terminal control characters. Small terminal excerpts are labeled and link to full logs. [artifact-provenance.json](artifact-provenance.json) records original and published hashes and transformations; the only path redaction replaces a local macOS temporary directory in a coverage-control message, preserving `NamedControl.lean`. Generic `/srv` and `/opt` paths are the verification environment's paths. Compiler record bytes are preserved inside a deterministic archive. [SHA256SUMS](SHA256SUMS) covers the files as published in release `v1.0.0`.

Since release `v1.1.0`, the 28 `.lean` files in this directory use Lean's module system: each begins with a `module` header and a one-line module docstring, its imports, if any, are `public import`, and its body is in an `@[expose] public section`. Their statements and commands are unchanged. SHA256SUMS and the run records hash the original files; `git diff v1.0.0 -- Verification/Supplemental` shows the change.

Giant exported proof streams, executable/build artifacts, cloud-account metadata, SSH material, and unrelated bootstrap downloads are omitted. The selected source and supplied audit inputs allow those proof exports to be regenerated. The archive and summaries document completed runs; they do not themselves re-execute Lean or certify a later proof commit.
