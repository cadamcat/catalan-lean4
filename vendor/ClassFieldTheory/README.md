# Ported ClassFieldTheory sources

This directory contains 871 Lean modules selected from
[n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory),
at source commit `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f`. This subset includes
540 ClassFieldTheory, 257 ValuedFieldTheory, and 74 GaloisCohomology modules.

The files were updated from upstream port commit
`7713795234690681b4406ae198b07aa95e82716a` for Lean `v4.35.0-rc3`, the module
system, and Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`. Each
modified file carries an upstream-change notice before its `module` header.
[SOURCES.json](SOURCES.json) records the original and port commits and paths and
the patch used to reconstruct each retained file. The patch is checked against
the original vendor snapshot at project commit
`c08bf727e7e0f773edd2f4777fd0d12152f44ed6`; [check_vendor.py](../../scripts/check_vendor.py)
replays it and reports any file that does not match. The original
[Apache-2.0 license](LICENSE) is preserved.

The top-level Lake project uses Lean/Mathlib `v4.35.0-rc3` and `--trust=0`.
Only the ClassFieldTheory library has a bounded `maxHeartbeats=1000000` setting.
The selected source revision is fixed and is not updated automatically. The
upstream project's Lake configuration is not used.
