#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
mkdir -p verification-results
python3 scripts/check_vendor.py
lake build Catalan.Audit 2>&1 | tee verification-results/build.log
lake env lean --trust=0 Catalan/Audit.lean 2>&1 | tee verification-results/audit.log
python3 scripts/check_axioms.py Catalan/Audit.lean verification-results/audit.log
lake env lean --trust=0 Verification/Axioms.lean 2>&1 | tee verification-results/top-level.log
python3 scripts/check_axioms.py Verification/Axioms.lean verification-results/top-level.log
lake env lean --trust=0 Verification/Statements.lean 2>&1 | tee verification-results/statements.log
python3 scripts/check_axioms.py Verification/Statements.lean verification-results/statements.log
