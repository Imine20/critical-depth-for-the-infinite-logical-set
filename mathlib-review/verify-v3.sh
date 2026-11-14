#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)"
out=${1:?Provide an absolute path to a task-owned build output directory}
case "$out" in
  /*) ;;
  *) printf '%s\n' 'Expected an absolute output path' >&2; exit 2 ;;
esac
mkdir -p "$out"
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
export LEAN_NUM_THREADS=1
lean --version > "$out/toolchain.txt"
grep -F 'version 4.35.0,' "$out/toolchain.txt"
grep -F 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' "$out/toolchain.txt"
modules='CriticalDepthMathlib SourceConsumer EncodedInverse Manuscript20261114Baseline GenerationThresholds RealAlgebraicImage BarePauliRotations FaultDepthArithmetic FaultProbability FaultHistoryLoss FaultChoiBound PauliSyndromeOptimization FaultCircuitSupport OrthogonalRecovery RecoveryCrossTerms Q37BinaryData Q37DistanceData Manuscript20261114Audit'
for module in $modules; do
  sha256sum "$module.lean"
done > "$out/inputs.sha256"
sha256sum lean-toolchain lake-manifest.json >> "$out/inputs.sha256"
for module in $modules; do
  printf '%s\n' "Checking $module"
  lean -j1 -M6144 -DmaxHeartbeats=3000000 -R . -o "$out/$module.olean" "$module.lean" > "$out/$module.log" 2>&1
done
sha256sum -c "$out/inputs.sha256"
grep -F V3_RECURSIVE_AUDIT_PASSED "$out/Manuscript20261114Audit.log"
if grep -E 'uses .sorry.|sorryAx|depends on axioms:.*native_decide' "$out"/*.log; then
  exit 1
fi
