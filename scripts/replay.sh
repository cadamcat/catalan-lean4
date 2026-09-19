#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
mkdir -p verification-results
lake build Catalan
lake env lean --trust=0 --run Verification/Replay.lean 2>&1 | tee verification-results/replay.log
