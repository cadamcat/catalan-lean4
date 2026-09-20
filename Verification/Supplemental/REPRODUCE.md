# Reading and reproducing the supplemental checks

The checked proof is commit `897079dab4c8dc980cc9b98ab28fed846e4a756f`. Keep a copy of this supplemental directory outside any checkout you switch to that commit: these evidence files were added later.

## Reproduce the public mathematical checks

In a fresh checkout of the selected proof commit, with its pinned Lean toolchain:

```sh
git clone https://github.com/cadamcat/catalan-lean4.git
cd catalan-lean4
git checkout --detach 897079dab4c8dc980cc9b98ab28fed846e4a756f
lake exe cache get
./scripts/verify.sh
./scripts/replay.sh
```

This workflow uses upstream dependency caches and rebuilds the submitted project. Do not run `lake update`. For the original commands and meanings, see [the guide at the selected proof commit](https://github.com/cadamcat/catalan-lean4/blob/897079dab4c8dc980cc9b98ab28fed846e4a756f/docs/verification.md); its historical statement about mandatory JSP self-checking has since been superseded by the [current verification guide](../../docs/verification.md).

## Additional comparator inputs and tool versions

Both runs used these fixed tool sources:

| Tool | Source commit |
|---|---|
| comparator | [`3927ad383f208ae977c340a91c48ac9b497d2097`](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097) |
| lean4export | [`15f6055e299ad5b89345e533cc2192f4cc00f659`](https://github.com/leanprover/lean4export/tree/15f6055e299ad5b89345e533cc2192f4cc00f659) |
| landrun | [`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4) |
| nanoda_lib | [`4c544ed4099c8227f07d5de77ad1e69fb0740a27`](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27) |

Recorded [source identities](common/evidence/tool-source-identity.txt) and [binary hashes](common/evidence/checker-binaries.sha256) accompany the results. The JSP audit helper came from [awards commit 38e63c4](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify/scripts/audit.py); it is not duplicated here. Original third-party licenses apply to those tools.

The [challenge](common/audit/StrictChallenge.lean) uses core operations and contains intentional specification placeholders. The [solution adapter](common/audit/StrictSolution.lean) imports the proof, not the challenge. In the isolated test checkout they were copied to `Catalan/StrictChallenge.lean` and `Catalan/StrictSolution.lean`. [config.json](common/audit/config.json) selects all five targets and permits only the three standard axioms. Run them with the pinned comparator's documented setup. The submitted proof must not import the challenge or the [negative-control projects](common/audit/controls/).

[targets.json](common/audit/targets.json) is the original audit-helper input. Its `coverage: pending` fields are preflight labels; they were not rewritten into a maintainer verdict. The target definitions, comparator results, and statement correspondence described in the PR provide the reported semantic evidence. Helper result paths refer to the original disposable Linux environment.

## Recorded strict and source-build environments

The runs used disposable Ubuntu 24.04 Linux environments with systemd, x86-64 AMD EPYC 9B45 processors, and a non-root verifier user. Generic runtime roots were `/srv/catalan-proof`, `/srv/catalan-audit`, `/opt/lean-4.33.1`, and `/opt/catalan-checkers`.

The following files preserve the actual commands and setup logic. They are historical run artifacts, not a single supported installer; the setup scripts modify users, file permissions, and firewall rules and belong only in an isolated verification environment.

- Strict run: [cache preparation](strict/tools/prepare-cache.sh), [socket probes](strict/tools/run-probes.py), [protected first build](strict/tools/seal-and-run.py), [control runner](strict/tools/run-controls.py), and [supplemental checks](strict/tools/supplemental.sh).
- Source run: [tool bootstrap](source/tools/bootstrap.sh), [fixed-source preparation](source/tools/prepare-source.py), [initial stage driver](source/tools/run-stages.py), and [successful post-Mathlib continuation](source/tools/run-after-mathlib.py). Actual per-stage commands and exit codes are in the accompanying result JSON files.
- Recorder history: [first Python wrapper](source/tools/lean-wrapper-v1.py), [second wrapper](source/tools/lean-wrapper-v2.py), [final wrapper](source/tools/lean-wrapper.py), [ELF launcher](source/tools/tool-launcher.c), and its [installation script](source/tools/install-elf-wrappers.py). Use the result/fix records to interpret which revision was active; executing every archived script in filename order does not recreate the run.

The source run cloned every dependency at the selected manifest SHA, built the required ProofWidgets frontend, disabled Lean package-cache retrieval, and compiled the Mathlib library before comparator compiled original Catalan/vendor modules. The official compiler distribution was retained. The later all-vendor target reused that run's fresh outputs; actual coverage comes from the compiler records, not its short elapsed time or replayed build output.

For a new reproduction, follow the current checker setup requirements and record any environment changes. The historical success logs are evidence for the recorded version, not a promise that cloud images or system packages will remain unchanged.

## Check and inspect this archive

From this supplemental directory on Linux:

```sh
sha256sum -c SHA256SUMS
cat source/evidence/build-coverage.json
gzip -dc source/evidence/compiled-source-inventory.json.gz
tar -tzf source/compiler-invocations.tar.gz
```

On macOS, `shasum -a 256 -c SHA256SUMS` provides the checksum check. The invocation archive contains only the two original record directories and regular JSON files. Its [member manifest](source/compiler-record-manifest.json.gz) identifies every record by SHA-256. The [coverage checker](source/tools/check-build-coverage.py) shows how successful source compilations were selected; its full filesystem/output check requires the reconstructed build tree, not just this evidence archive.

Checksums establish package integrity, not mathematical correctness. Reproduce the selected proof and audit its statements and dependencies to establish those claims independently.
