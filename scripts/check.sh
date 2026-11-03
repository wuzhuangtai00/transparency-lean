#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p validation
lake build 2>&1 | tee validation/build.log
# Trust level zero rechecks imported proof terms as well.
lake env lean --trust=0 TransparencyLean/Certificate.lean 2>&1 | tee validation/axioms.log
python3 scripts/check_axioms.py validation/axioms.log | tee validation/audit.log
