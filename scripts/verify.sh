#!/bin/sh
# Current single-file verification. Resource isolation belongs to the caller.
# Source-built mode never invokes Lake; see docs/DEPENDENCY_SOURCE_REPLAY.md.
set -eu
set -f
proof_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$proof_root"
proof_mode=${CRITICAL_DEPTH_DEPENDENCY_MODE:-lake-cache}
proof_receipt='-'
proof_registry=mathlib-review/AUDIT_EXPECTED.txt
test -s lake-manifest.json
test -s mathlib-review/CriticalDepthMathlib.lean
test -s "$proof_registry"
cmp lean-toolchain mathlib-review/lean-toolchain
cmp lake-manifest.json mathlib-review/lake-manifest.json
(cd mathlib-review && sha256sum -c PAYLOAD_SHA256.txt)

case "$proof_mode" in
  trusted-cache)
    : "${CRITICAL_DEPTH_LEAN:?trusted-cache mode requires an explicit Lean executable}"
    : "${CRITICAL_DEPTH_PUBLIC_LEAN_PATH:?trusted-cache mode requires nine pinned public cache roots}"
    if [ -n "${CRITICAL_DEPTH_SOURCE_BUILD_RECEIPT:-}" ]; then
      printf 'Trusted-cache mode must not carry a source-build receipt.\n' >&2
      exit 2
    fi
    proof_lean=$CRITICAL_DEPTH_LEAN
    proof_paths=$CRITICAL_DEPTH_PUBLIC_LEAN_PATH
    ;;
  source-built)
    : "${CRITICAL_DEPTH_LEAN:?source-built mode requires an explicit Lean executable}"
    : "${CRITICAL_DEPTH_PUBLIC_LEAN_PATH:?source-built mode requires nine public output roots}"
    : "${CRITICAL_DEPTH_SOURCE_BUILD_RECEIPT:?source-built mode requires source-dependencies.json}"
    proof_lean=$CRITICAL_DEPTH_LEAN
    proof_paths=$CRITICAL_DEPTH_PUBLIC_LEAN_PATH
    proof_receipt=$CRITICAL_DEPTH_SOURCE_BUILD_RECEIPT
    test -s "$proof_receipt"
    ;;
  lake-cache)
    if [ -n "${CRITICAL_DEPTH_PUBLIC_LEAN_PATH:-}" ] ||
       [ -n "${CRITICAL_DEPTH_SOURCE_BUILD_RECEIPT:-}" ]; then
      printf 'Explicit public outputs require CRITICAL_DEPTH_DEPENDENCY_MODE=source-built.\n' >&2
      exit 2
    fi
    if [ -n "${CRITICAL_DEPTH_LEAN:-}" ]; then
      proof_lean=$CRITICAL_DEPTH_LEAN
    else
      proof_prefix=$(lake env lean --print-prefix)
      proof_lean="$proof_prefix/bin/lean"
    fi
    # Lake configuration/environment inspection; no Lake build is requested.
    proof_paths=$(lake env sh -c 'printf "%s" "$LEAN_PATH"')
    ;;
  *) printf 'Unknown dependency mode.\n' >&2; exit 2 ;;
esac
case "$proof_lean" in /*) ;; *) printf 'Lean executable must be an absolute path.\n' >&2; exit 2 ;; esac
proof_lean=$(realpath "$proof_lean")
test -x "$proof_lean"
proof_version=$("$proof_lean" --version)
case "$proof_version" in
  *'version 4.35.0,'*'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'*) ;;
  *) printf 'Unexpected Lean toolchain.\n' >&2; exit 2 ;;
esac
proof_prefix=$("$proof_lean" --print-prefix)

# The two-line registry binds the exact expected counters to this source.
# It is committed/payload-bound; callers cannot replace its values by flags.
test "$(grep -c '^source_sha256=' "$proof_registry")" -eq 1
test "$(grep -c '^audit_marker=' "$proof_registry")" -eq 1
grep -Eq '^source_sha256=[0-9a-f]{64}$' "$proof_registry"
proof_expected_source=$(sed -n 's/^source_sha256=//p' "$proof_registry")
proof_source_hash=$(sha256sum mathlib-review/CriticalDepthMathlib.lean | cut -d ' ' -f 1)
test "$proof_expected_source" = "$proof_source_hash"
proof_expected=$(sed -n 's/^audit_marker=//p' "$proof_registry")
printf '%s\n' "$proof_expected" | grep -Eq '^STANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED theorem_count=[1-9][0-9]* constant_count=[1-9][0-9]* target_count=[1-9][0-9]* exact_three_count=[0-9]+ proposition_check_count=[0-9]+ foundation_count=[0-9]+ own_axiom_count=0 imported_project_module_count=0 unapproved_import_count=0$'

proof_run_root="$proof_root/.verification/current"
mkdir -p "$proof_run_root"
test ! -L "$proof_run_root"
test "$(realpath "$proof_run_root")" = "$proof_run_root"
proof_out=$(mktemp -d "$proof_run_root/run.XXXXXXXX")
printf '%s\n' "$proof_mode" > "$proof_out/dependency-mode.txt"
printf '%s\n' "$proof_version" > "$proof_out/toolchain.txt"
printf '%s\n' "$proof_expected" > "$proof_out/expected-audit-marker.txt"

# Local path records are deliberately separate from portable math/hash output.
# Do not publish the .verification directory as release evidence.
printf '%s\n' "$proof_lean" "$proof_prefix" > "$proof_out/toolchain-paths.local.txt"
sha256sum mathlib-review/CriticalDepthMathlib.lean mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md lean-toolchain lakefile.toml \
  lake-manifest.json scripts/verify.sh scripts/verify_public_dependencies.pl \
  "$proof_registry" mathlib-review/PAYLOAD_SHA256.txt \
  manuscript/shallow_logical_operators_depth_threshold.tex \
  "$proof_lean" > "$proof_out/inputs-before.local.sha256"
if [ "$proof_mode" = source-built ]; then
  sha256sum "$proof_receipt" >> "$proof_out/inputs-before.local.sha256"
fi

# In source-built mode this checks every part against the bound source receipt,
# rejects unreceipted artifacts/symlinks/native libraries, and checks lock pins.
# In cache mode it selects only the locked packages' Lake output directories.
perl scripts/verify_public_dependencies.pl "$proof_mode" "$proof_root" \
  "$proof_paths" "$proof_receipt" "$proof_prefix" \
  "$proof_out/public-artifacts.before.jsonl" "$proof_out/LEAN_PATH.local.txt" \
  > "$proof_out/dependency-check.before.txt"
proof_public_path=$(cat "$proof_out/LEAN_PATH.local.txt")
export LEAN_PATH="$proof_public_path"
export LEAN_NUM_THREADS=1
unset LEAN_SRC_PATH

proof_status=0
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$proof_out/compiler-start.utc"
"$proof_lean" -j 1 -M 6144 -DmaxHeartbeats=3000000 \
  -R mathlib-review -o "$proof_out/CriticalDepthMathlib.olean" \
  -i "$proof_out/CriticalDepthMathlib.ilean" \
  mathlib-review/CriticalDepthMathlib.lean \
  > "$proof_out/CriticalDepthMathlib.log" 2>&1 || proof_status=$?
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$proof_out/compiler-end.utc"
printf '%s\n' "$proof_status" > "$proof_out/exit.txt"
if [ "$proof_status" -eq 0 ] &&
   sha256sum -c "$proof_out/inputs-before.local.sha256" > "$proof_out/input-binding.local.txt" &&
   (cd mathlib-review && sha256sum -c PAYLOAD_SHA256.txt) > "$proof_out/payload-binding.after.txt" &&
   perl scripts/verify_public_dependencies.pl "$proof_mode" "$proof_root" \
     "$proof_paths" "$proof_receipt" "$proof_prefix" \
     "$proof_out/public-artifacts.after.jsonl" "$proof_out/LEAN_PATH.after.local.txt" \
     > "$proof_out/dependency-check.after.txt" &&
   cmp "$proof_out/LEAN_PATH.local.txt" "$proof_out/LEAN_PATH.after.local.txt" &&
   cmp "$proof_out/public-artifacts.before.jsonl" "$proof_out/public-artifacts.after.jsonl" &&
   test -s "$proof_out/CriticalDepthMathlib.olean" &&
   test -s "$proof_out/CriticalDepthMathlib.ilean" &&
   test "$(grep -c '^STANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED ' "$proof_out/CriticalDepthMathlib.log")" -eq 1 &&
   grep '^STANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED ' "$proof_out/CriticalDepthMathlib.log" \
     > "$proof_out/final-audit-marker.txt" &&
   cmp "$proof_out/expected-audit-marker.txt" "$proof_out/final-audit-marker.txt"; then
  (cd "$proof_out" && sha256sum CriticalDepthMathlib.olean CriticalDepthMathlib.ilean) \
    > "$proof_out/artifact.sha256"
  cat "$proof_out/final-audit-marker.txt"
  printf 'CURRENT_SOURCE_AUDIT_PASSED dependency_mode=%s source_sha256=%s\n' "$proof_mode" "$proof_source_hash"
else
  # The directory was freshly allocated by this script; preserve rejected logs.
  rm -f "$proof_out/CriticalDepthMathlib.olean" "$proof_out/CriticalDepthMathlib.olean.private" \
    "$proof_out/CriticalDepthMathlib.olean.server" "$proof_out/CriticalDepthMathlib.ir" \
    "$proof_out/CriticalDepthMathlib.ir.sig" "$proof_out/CriticalDepthMathlib.ilean"
  printf 'Current source verification rejected; local diagnostic records retained.\n' >&2
  if [ "$proof_status" -ne 0 ]; then exit "$proof_status"; fi
  exit 2
fi
