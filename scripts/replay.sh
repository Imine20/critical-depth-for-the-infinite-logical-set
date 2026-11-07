#!/bin/sh
# Run the source audit and a separate caller against its fresh proof artifact.
# Run this in a clean checkout with the locked dependencies already available.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)"

kernel_replay=${CRITICAL_DEPTH_KERNEL_REPLAY:-0}
case $kernel_replay in
  0|1) ;;
  *) printf '%s\n' 'CRITICAL_DEPTH_KERNEL_REPLAY must be 0 or 1.' >&2; exit 2 ;;
esac

for previous in .verification/current/run.*; do
  if [ -e "$previous" ]; then
    printf '%s\n' 'Use a fresh checkout or move the previous .verification directory aside.' >&2
    exit 2
  fi
done
mkdir -p .verification
out=$(mktemp -d "$PWD/.verification/replay.XXXXXXXX")
printf 'Replay evidence: %s\n' "$out"

if sh scripts/verify.sh > "$out/main-driver.log" 2>&1; then
  cat "$out/main-driver.log"
else
  rc=$?
  cat "$out/main-driver.log" >&2
  exit "$rc"
fi

set -- "$PWD"/.verification/current/run.*
test "$#" -eq 1
test -d "$1"
main=$1
(cd "$main" && sha256sum -c artifact.sha256)
(
  cd "$main"
  for artifact in CriticalDepthMathlib.olean* CriticalDepthMathlib.ilean CriticalDepthMathlib.ir*; do
    if [ -f "$artifact" ]; then sha256sum "$artifact"; fi
  done
) > "$out/main-artifacts.sha256"
printf '%s\n' "$main" > "$out/main-path.local.txt"

lean=$(sed -n '1p' "$main/toolchain-paths.local.txt")
public_paths=$(cat "$main/LEAN_PATH.local.txt")
export LEAN_PATH="$out:$main:$public_paths"
export LEAN_NUM_THREADS=1
unset LEAN_SRC_PATH

"$lean" -j 1 -M 6144 -DmaxHeartbeats=3000000 -R mathlib-review \
  -o "$out/SourceConsumer.olean" -i "$out/SourceConsumer.ilean" \
  mathlib-review/SourceConsumer.lean > "$out/SourceConsumer.log" 2>&1
test "$(grep -c '^TRUSTED_CACHE_EXTERNAL_CONSUMER_PASSED ' "$out/SourceConsumer.log")" -eq 1
grep -Fx 'TRUSTED_CACHE_EXTERNAL_CONSUMER_PASSED call_count=3 imported_main_count=2 exact_three_count=5' \
  "$out/SourceConsumer.log" > "$out/consumer-marker.txt"
(cd "$main" && sha256sum -c "$out/main-artifacts.sha256")
(
  cd "$out"
  for artifact in SourceConsumer.olean* SourceConsumer.ilean SourceConsumer.ir*; do
    if [ -f "$artifact" ]; then sha256sum "$artifact"; fi
  done
) > "$out/consumer-artifacts.sha256"
cat "$out/consumer-marker.txt"
printf '%s\n' SOURCE_AUDIT_AND_CALLER_PASSED

if [ "$kernel_replay" = 1 ]; then
  toolchain_bin=$(dirname -- "$lean")
  checker="$toolchain_bin/leanchecker"
  test -x "$checker"
  PATH="$toolchain_bin:$PATH" "$checker" -v CriticalDepthMathlib > "$out/leanchecker-main.log" 2>&1
  PATH="$toolchain_bin:$PATH" "$checker" -v SourceConsumer > "$out/leanchecker-caller.log" 2>&1
  (cd "$main" && sha256sum -c "$out/main-artifacts.sha256")
  (cd "$out" && sha256sum -c consumer-artifacts.sha256)
  printf '%s\n' BUNDLED_KERNEL_REPLAY_PASSED
fi
