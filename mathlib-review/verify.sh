#!/bin/sh
# Independent portable cache-based check. The repository root also supports
# a separately sealed from-source public-dependency mode.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)"
sha256sum -c PAYLOAD_SHA256.txt
mkdir -p .verification
out=$(mktemp -d .verification/cache-run.XXXXXXXX)
lake env lean --version > "$out/toolchain.txt"
grep -F 'version 4.35.0,' "$out/toolchain.txt"
grep -F 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' "$out/toolchain.txt"
expected_source=$(sed -n 's/^source_sha256=//p' AUDIT_EXPECTED.txt)
expected_marker=$(sed -n 's/^audit_marker=//p' AUDIT_EXPECTED.txt)
test "$(sha256sum CriticalDepthMathlib.lean | cut -d ' ' -f 1)" = "$expected_source"
sha256sum CriticalDepthMathlib.lean ALIGNED_MATHEMATICAL_STATEMENTS.md AUDIT_EXPECTED.txt PAYLOAD_SHA256.txt > "$out/inputs-before.sha256"
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$out/start"
status=0
lake env lean -j 1 -M 6144 -DmaxHeartbeats=3000000 -R . \
  -o "$out/CriticalDepthMathlib.olean" -i "$out/CriticalDepthMathlib.ilean" \
  CriticalDepthMathlib.lean > "$out/CriticalDepthMathlib.log" 2>&1 || status=$?
printf '%s\n' "$status" > "$out/exit.txt"
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$out/end"
[ "$status" -eq 0 ] || exit "$status"
sha256sum -c "$out/inputs-before.sha256" > "$out/input-binding.txt"
sha256sum -c PAYLOAD_SHA256.txt > "$out/payload-binding.txt"
test "$(grep -c '^STANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED ' "$out/CriticalDepthMathlib.log")" -eq 1
grep '^STANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED ' "$out/CriticalDepthMathlib.log" > "$out/actual-marker.txt"
printf '%s\n' "$expected_marker" > "$out/expected-marker.txt"
cmp "$out/actual-marker.txt" "$out/expected-marker.txt"
(cd "$out" && sha256sum CriticalDepthMathlib.olean CriticalDepthMathlib.ilean) > "$out/artifact.sha256"
cat "$out/actual-marker.txt"
printf '%s\n' CURRENT_PORTABLE_CHECK_PASSED_DEPENDENCY_MODE_LAKE_CACHE
