# Palomar port report

Run date: 2026-10-05. Branch: `palomar`. Implementation HEAD checked: `e0e69f2`. All work is local; the main checkout was not touched. No push, pull request, issue, GitHub Actions run, Palomar API request, or submission was made.

## Toolchain and dependency revisions

| Component | Revision |
| --- | --- |
| Project Lean toolchain | `leanprover/lean4:v4.35.0-rc3` |
| Lean compiler commit | `470d5ce1400764999581fd26d5d72b00d990b0f4` (arm64-apple-darwin24.6.0) |
| Lake | `5.0.0-src+470d5ce` |
| Mathlib | `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`; its `lean-toolchain` exactly matches the project's |
| ClassFieldTheory source snapshot | `n-yamaguchi-0729/ClassFieldTheory`, commit `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f` |
| Upstream ClassFieldTheory Lean 4.35 port | commit `7713795234690681b4406ae198b07aa95e82716a` (targets Lean 4.35.0-rc2) |
| Comparator | `leanprover/comparator`, commit `fd5d5bcf14177b187f66d4502071268d877887c3` |
| lean4export | tag `v4.35.0-rc3`, commit `66f1fb4bc256072069767fce52d39480e4524869` |
| NanoDa source | `ammkrn/nanoda_lib`, commit `3a2407216ee84a75f9e1aead6803d0578be06ae7` |

Mathlib and its dependencies were obtained with `lake exe cache get`; the measured project build used that cache and compiled the project, Catalan, and vendored sources from source.

Upgrade commands were `lake update` and `lake exe cache get`; both completed successfully, and the new `lake-manifest.json` is committed.

## Upgrade, port, and module system

- The root `lean-toolchain` is `leanprover/lean4:v4.35.0-rc3`. The Mathlib manifest revision is `c55e6e786f49471c72fbddbec5415808896aec1e`, and the installed Mathlib `lean-toolchain` is the same `v4.35.0-rc3`.
- The original 871-file vendor subset is retained (540 ClassFieldTheory, 257 ValuedFieldTheory, 74 GaloisCohomology). The files were ported from the upstream rc2 branch to Mathlib rc3 and the Lean module/visibility system. Each changed file has a pre-`module` notice identifying the upstream port and change type. `THIRD_PARTY.md` records the Apache-2.0 notices and modifications.
- The upstream port adds and splits support modules that are outside this fixed subset. Required fractional-ideal norm/factorization declarations, finite-place unramified normalization, and two principal-unit quotient helpers were merged into retained files. The induced-function model from the separate `ProCGroups` subtree was inlined into the retained Herbrand module. These changes and reconstruction patches are recorded in `vendor/ClassFieldTheory/SOURCES.json`.
- `scripts/check_vendor.py` reconstructs all 871 retained files from the recorded original source and patch. The named disposable mutation control changes one byte of `AdeleBaseChange.lean` and fails naming `Lean4/ClassFieldTheory/AlgebraicNumberTheory/AdeleBaseChange.lean`.
- Commands and output: `python3 scripts/check_vendor.py` → `Reconstructed and verified 871 vendored ClassFieldTheory sources and the license.` `python3 -m unittest -v scripts/tests/test_vendor.py` → `test_one_byte_mutation_fails_for_named_vendored_file ... ok`.
- All 1,402 tracked `.lean` files have a module header and later module documentation; the largest is 3,024 physical lines. `Challenge.lean` is 48 lines/1,753 bytes, below the brief's stricter 300-line/32-KiB limit. `lakefile.toml` remains TOML.
- The five protected Catalan declaration types match the starting source: the axiom-result file is byte-for-byte unchanged from `c08bf72`, and the source diffs for the declarations and `Verification/Statements.lean` add the module/import/documentation/visibility prefix without changing their statements or proofs. The three statement restatements elaborate successfully.

## Full build and resources

The clean measured build used N=6, `LEAN_NUM_THREADS=6`, and the lane's `localrun` wrapper. Lake's `lake build --help` exposes no jobs/`-j` option. The build had six concurrent Lean processes, confirming the `LEAN_NUM_THREADS=6` scheduling cap for this run.

Command run by the monitor:

```sh
../localrun.sh -t 3600 -n 6 env LEAN_NUM_THREADS=6 \
  python3 ../build_monitor_palomar.py 6 ../build-full-palomar.log
```

The monitor ran:

```sh
/usr/bin/time -l lake build Catalan ClassFieldTheory ValuedFieldTheory \
  GaloisCohomology Verification Challenge Solution
```

Output:

```text
BUILD_WALL_SECONDS=1024.56
MAX_CONCURRENT_LEAN=6
PEAK_SINGLE_LEAN_RSS_KIB=3960400
PEAK_SINGLE_LEAN_RSS_GIB=3.777
N_TIMES_PEAK_GIB=22.662
MAX_AGGREGATE_LEAN_RSS_GIB=15.608
MEMORY_LIMIT_EXCEEDED=False
Build completed successfully (10338 jobs).
1024.27 real      5178.72 user      1563.89 sys
4058873856  maximum resident set size
```

The complete target command passed again after adding `@[expose] public section` to the Palomar modules:

```sh
../localrun.sh -t 3600 -n 6 env LEAN_NUM_THREADS=6 \
  lake build Catalan ClassFieldTheory ValuedFieldTheory GaloisCohomology \
  Verification Challenge Solution
```

It ended with `Build completed successfully (10338 jobs).` The clean measured build preceded this visibility-only source update; the final source was rebuilt by Comparator and by this all-target build.

## Axiom audit and replay

`./scripts/verify.sh`, run as `../localrun.sh -t 3600 -n 6 env LEAN_NUM_THREADS=6 ./scripts/verify.sh`, completed with:

```text
Reconstructed and verified 871 vendored ClassFieldTheory sources and the license.
Build completed successfully (10327 jobs).
verified 1390 axiom report(s); all roots and axioms are allowed
verified 5 axiom report(s); all roots and axioms are allowed
verified 3 axiom report(s); all roots and axioms are allowed
```

The five protected public theorems and the three `Verification.Statements` declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The replay reports the same set and no unsafe or partial declarations. A separate scan using `Verification.Replay.cone` reported `Lean.ofReduceBool in theorem cone: []`; `sorryAx` and custom axioms would fail the nonstandard-axiom check.

`./scripts/replay.sh`, run as `../localrun.sh -t 3600 -n 6 env LEAN_NUM_THREADS=6 ./scripts/replay.sh`, completed with:

```text
cone contains 131214 constants; all names have ConstantInfo
unsafe/partial constants in cone: []
axioms in cone: [Classical.choice, Quot.sound, propext]
nonstandard axioms in cone: []
all replayable cone constants are present in the replayed kernel environment
fresh-environment kernel replay of 131214 constants; verification passed = true
```

The five theorem roots were present after replay as theorems with identical types. Lean 4.35.0-rc3 emits a deprecation warning for `Lean.Environment.replay`; it did not prevent replay.

## Challenge, Solution, and Comparator

`Challenge.lean` imports Mathlib only and states `PalomarCatalan.catalans_conjecture`, `catalan_int`, `catalan_int_signed`, and `mihailescu_odd_primes`, each with a sorry placeholder and a statement-specific docstring. The first declaration matches Google DeepMind's Formal Conjectures statement. `Solution.lean` imports `Catalan`, not `Challenge`, and proves those same qualified names by applying the project theorems. Both modules expose their declarations. `comparator.json` contains only accepted keys and sets `permitted_axioms` to `propext`, `Quot.sound`, and `Classical.choice`; `enable_nanoda` is true.

A preliminary Comparator run passed using a temporary configuration with `enable_nanoda: false`. This checked exact statements, solution axioms, and the built-in Lean kernel; it is not the requested NanoDa-enabled run. Command:

```sh
COMPARATOR_LANDRUN=/tmp/palomar-tools/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/palomar-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
../localrun.sh -t 3600 -n 2 env LEAN_NUM_THREADS=2 lake env \
  /tmp/palomar-tools/comparator/.lake/build/bin/comparator \
  /tmp/palomar-tools/comparator-no-nanoda.json
```

Result: `Lean default kernel accepts the solution` and `Your solution is okay!`. The Comparator README's macOS development shim was used; its output warns that fake-landrun runs unsandboxed.

**NanoDa-enabled run:** passed on 2026-10-05, with the committed `comparator.json` (`enable_nanoda: true`) at commit `8038467`.

- **NanoDa** was built with `cargo build --release --locked` from `ammkrn/nanoda_lib` `3a2407216ee84a75f9e1aead6803d0578be06ae7`. Its dependencies came from the official crates.io registry, as the user authorized on 2026-10-05.
  - `Cargo.lock` SHA-256: `9b921e794ce5ed515eb31db9ada0c2f34df999b6c9b5135ad308a412872e42be`
  - `nanoda_bin` SHA-256: `89d2f7cca8b1f32de4b3b8ec4b3d60238ec83eefbc76e7f6370966a4c3e1021b`
- **Comparator** was `fd5d5bcf14177b187f66d4502071268d877887c3`; **lean4export** was `v4.35.0-rc3`, commit `66f1fb4bc256072069767fce52d39480e4524869`.
- **Command:**

```sh
COMPARATOR_LANDRUN=/tmp/palomar-tools/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/palomar-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
COMPARATOR_NANODA=/tmp/palomar-tools/nanoda/target/release/nanoda_bin \
../localrun.sh -t 3600 -n 6 env LEAN_NUM_THREADS=6 lake env \
  /tmp/palomar-tools/comparator/.lake/build/bin/comparator comparator.json
```

- **Result:** `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`, exit 0.
  - The exported constants were the four `PalomarCatalan` theorems and the three permitted axioms, plus the kernel's built-in names.
  - Wall time was 712 s (user 865 s), on Apple Silicon macOS with N = 6.
- **The sandbox was a shim.** The run used the Comparator README's macOS shim, which warns that it is not real Landrun and runs unsandboxed. Palomar's own verification runs on Linux with Landrun.
- **The full log** (872 lines) is kept outside the repository, in the workspace run record `nanoda-lane/comparator-nanoda.log`.

## Palomar policy notes and remaining preflight

- Palomar CONTRIBUTING §2.2 defines a hard 100-KiB/1,000-line Challenge cap and a warning above 32 KiB/300 lines; the brief's stricter 32-KiB/300-line limit is satisfied.
- CONTRIBUTING §2.3 accepts `enable_nanoda` as an optional Comparator key but states that its submitted value is non-authoritative: Palomar supplies its own protected NanoDa config. The committed value is true for the requested local run; it does not select registry verification behavior.
- The brief excludes `Catalan.JSP.statement` from Challenge because it requires the project's proper-perfect-power definition. It is still in the project's five-root verification and kernel replay.
- CONTRIBUTING §2's ordinary layout includes `formalization.yaml`, which this brief assigns to the main session. This lane did not write it. The full Palomar preflight requires the registry's prescribed reusable workflow on the exact repository revision and paths; the Palomar submit documentation says a local `lake build` or standalone Comparator run is not equivalent. No GitHub Actions run, API call, or submission was authorized here.

## Facts for `formalization.yaml`

- Lean toolchain: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib revision: `c55e6e786f49471c72fbddbec5415808896aec1e` (`v4.35.0-rc3`).
- Challenge module: `Challenge`; Solution module: `Solution`.
- Compared names: `PalomarCatalan.catalans_conjecture`, `PalomarCatalan.catalan_int`, `PalomarCatalan.catalan_int_signed`, and `PalomarCatalan.mihailescu_odd_primes`.
- Existing protected declarations remain `Catalan.catalans_conjecture`, `Catalan.catalan_int`, `Catalan.catalan_int_signed`, `Catalan.mihailescu_odd_primes`, and `Catalan.JSP.statement`. The JSP statement is intentionally excluded from Challenge.
- Vendor provenance: 871 source paths from `n-yamaguchi-0729/ClassFieldTheory` commit `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f`, adapted from port commit `7713795234690681b4406ae198b07aa95e82716a` and Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`; Apache-2.0 license preserved.
- The paper-cited original release remains `v1.0.0` (`4bf1f74`); `paper/` and release tags were not changed.
