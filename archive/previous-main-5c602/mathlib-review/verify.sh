#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
sha256sum -c PAYLOAD_SHA256.txt
mkdir -p .verification
lake env lean --version > .verification/toolchain.txt
cat .verification/toolchain.txt
grep -F 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' .verification/toolchain.txt
sha256sum CriticalDepthMathlib.lean > .verification/source-before.sha256
rm -f .verification/CriticalDepthMathlib.olean .verification/CriticalDepthMathlib.olean.private .verification/CriticalDepthMathlib.olean.server
if lake env lean -j 1 -M 6144 -DmaxHeartbeats=3000000 \
  -o .verification/CriticalDepthMathlib.olean CriticalDepthMathlib.lean \
  > .verification/CriticalDepthMathlib.log 2>&1; then
  printf '0\n' > .verification/exit.txt
else
  status=$?
  printf '%s\n' "$status" > .verification/exit.txt
  rm -f .verification/CriticalDepthMathlib.olean .verification/CriticalDepthMathlib.olean.private .verification/CriticalDepthMathlib.olean.server
  cat .verification/CriticalDepthMathlib.log
  exit "$status"
fi
sha256sum -c .verification/source-before.sha256
marker='STANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED theorem_count=1251 constant_count=1727 target_count=29 exact_three_count=17 proposition_check_count=12 foundation_count=12 own_axiom_count=0 imported_project_module_count=0 unapproved_import_count=0'
test "$(grep -Fc "$marker" .verification/CriticalDepthMathlib.log)" = 1
grep -Fx "$marker" .verification/CriticalDepthMathlib.log
