#!/usr/bin/env bash
# The gate: docs/spec/milestone-1.md § Verification.
set -euo pipefail
cd "$(dirname "$0")/.."

step() { printf '\n== %s\n' "$*"; }

step "1. no @unsafe or foreign import outside kernel/main.bend"
if grep -rnE '@unsafe|^\s*def\s+\S+\?\(|^\s*import\s+"' kernel --include='*.bend' | grep -v '^kernel/main.bend:'; then
  echo "FAIL: unsafe or foreign code outside kernel/main.bend"
  exit 1
fi

step "2. bend kernel/PROOF.bend"
timeout 1500 bend kernel/PROOF.bend

step "3. bend kernel/PROOF.bend --verdict"
timeout 1500 bend kernel/PROOF.bend --verdict

step "4. kernel tests"
scripts/test-kernel.sh

if [ -d edge ]; then
  step "5. cargo test (edge)"
  (cd edge && timeout 1500 cargo test --quiet)
else
  step "5. cargo test: no edge/ yet"
fi

step "6. acceptance list"
python3 -I scripts/acceptance.py

step "7. ngap: generated code is current and agrees with pycrate on the NGAP vectors"
python3 -I tools/ngap-gen/test_gen.py
python3 -I tools/ngap-gen/oracle.py

echo
echo "CHECK OK"
