#!/bin/sh
# Run from the locked workspace using: lake env sh scripts/verify.sh
# This script serializes project elaboration. An aggregate resource boundary,
# when required, must enclose Lake and all descendants as well as this script.
set -eu
proof_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$proof_root"
test -s lake-manifest.json
test -n "${LEAN_PATH:-}" || { printf 'Use: lake env sh scripts/verify.sh\n'; exit 2; }
proof_prefix=$(lean --print-prefix)
proof_lean="$proof_prefix/bin/lean"
proof_version=$("$proof_lean" --version)
case "$proof_version" in
  *'version 4.35.0,'*'eb6cafb7290e'*) ;;
  *) printf 'Unexpected Lean executable: %s\n' "$proof_version"; exit 2 ;;
esac
export LEAN_NUM_THREADS=1
proof_stamp=$(date -u '+%Y%m%dT%H%M%SZ')
proof_out="$proof_root/.verification/$proof_stamp"
mkdir -p "$proof_out" .lake/build/lib/lean/CriticalDepth
proof_artifacts="$proof_root/.lake/build/lib/lean"
test "$(realpath "$proof_artifacts")" = "$proof_artifacts" || {
  printf 'Artifact directory must resolve inside this workspace.\n'; exit 2;
}
test ! -L "$proof_artifacts/CriticalDepth" || exit 2
if find "$proof_artifacts/CriticalDepth" -type l -print | grep -q .; then
  printf 'Unexpected symlink inside project artifact namespace.\n'; exit 2
fi
proof_saved_ifs=$IFS
IFS=:
for proof_path_entry in $LEAN_PATH; do
  if [ "$proof_path_entry" != "$proof_artifacts" ] &&
      { [ -d "$proof_path_entry/CriticalDepth" ] || [ -f "$proof_path_entry/CriticalDepth.olean" ]; }; then
    printf 'Another CriticalDepth artifact tree is on LEAN_PATH: %s\n' "$proof_path_entry"; exit 2
  fi
done
IFS=$proof_saved_ifs
export LEAN_PATH="$proof_artifacts:$LEAN_PATH"
printf '%s\n' "$proof_version" > "$proof_out/toolchain.txt"
sha256sum "$proof_lean" > "$proof_out/executable.sha256"
printf '%s\n' "$LEAN_PATH" > "$proof_out/LEAN_PATH.txt"
sha256sum CriticalDepth.lean CriticalDepth/*.lean lean-toolchain lakefile.toml scripts/verify.sh \
  lake-manifest.json manuscript/shallow_logical_operators_depth_threshold.tex \
  > "$proof_out/sources-before.sha256"

# Topological order of every project proof/example module. Audit is last.
proof_modules='
Arithmetic ComponentConstants DerivationExtension IntegralImage MatrixCore
MatrixDerivation AlgebraicFrame AlgebraicRigidity ArithmeticExamples Compression
FieldConstants ManuscriptStatements ProjectiveFaithfulness Rotations DepthZero
PauliTensor ProjectiveTopology RotationExamples ScalarConstants Support
AlgebraicFiniteImage CircuitParameters LayerOperations PauliSpan ScalarExtension
CircuitNormalization FieldLightCone LocalScalarCoordinates PauliConjugation
StabilizerWitness CircuitSolutions FieldLayerDerivative FourQubitExample
PauliCompression CircuitPoints FourQubitStabilizer InsertionDetection PauliSynthesis
PhysicalCompressionExample TheoremOne TheoremTwoReduction BudgetSemantics
MainResults MainExamples PositiveDepth PositiveDepthExamples Audit'
find CriticalDepth -type f -name '*.lean' -print | \
  sed -e 's#^CriticalDepth/##' -e 's#/#.#g' -e 's#\.lean$##' | sort \
  > "$proof_out/discovered-modules.txt"
printf '%s\n' $proof_modules | sort > "$proof_out/scheduled-modules.txt"
cmp "$proof_out/discovered-modules.txt" "$proof_out/scheduled-modules.txt" || {
  printf 'Project module set changed; update the checked dependency order.\n'; exit 2;
}
# Clear all prior project artifacts before elaborating any module. The checked
# absolute directory above belongs exclusively to this package's namespace.
find "$proof_artifacts/CriticalDepth" -type f \
  \( -name '*.olean' -o -name '*.olean.private' -o -name '*.olean.server' -o -name '*.ilean' \) -delete
rm -f "$proof_artifacts/CriticalDepth.olean" \
  "$proof_artifacts/CriticalDepth.olean.private" "$proof_artifacts/CriticalDepth.olean.server"
for proof_module in $proof_modules; do
  proof_source="CriticalDepth/$proof_module.lean"
  proof_target=".lake/build/lib/lean/CriticalDepth/$proof_module.olean"
  printf 'Checking CriticalDepth.%s\n' "$proof_module"
  rm -f "$proof_target" "$proof_target.private" "$proof_target.server"
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$proof_out/$proof_module.start"
  printf '%s\n' "$proof_lean -j 1 -M 6144 -DmaxHeartbeats=3000000 -o $proof_target $proof_source" \
    > "$proof_out/$proof_module.command.txt"
  if "$proof_lean" -j 1 -M 6144 -DmaxHeartbeats=3000000 \
      -o "$proof_target" "$proof_source" > "$proof_out/$proof_module.log" 2>&1; then
    printf '0\n' > "$proof_out/$proof_module.exit"
  else
    proof_status=$?
    printf '%s\n' "$proof_status" > "$proof_out/$proof_module.exit"
    rm -f "$proof_target" "$proof_target.private" "$proof_target.server"
    cat "$proof_out/$proof_module.log"
    exit "$proof_status"
  fi
  for proof_artifact in "$proof_target" "$proof_target.private" "$proof_target.server"; do
    if [ -f "$proof_artifact" ]; then
      sha256sum "$proof_artifact" >> "$proof_out/project-artifacts.sha256"
    fi
  done
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$proof_out/$proof_module.end"
done
if "$proof_lean" -j 1 -M 6144 -DmaxHeartbeats=3000000 \
  -o .lake/build/lib/lean/CriticalDepth.olean CriticalDepth.lean \
  > "$proof_out/entry-point.log" 2>&1; then
  printf '0\n' > "$proof_out/entry-point.exit"
else
  proof_status=$?
  printf '%s\n' "$proof_status" > "$proof_out/entry-point.exit"
  rm -f .lake/build/lib/lean/CriticalDepth.olean \
    .lake/build/lib/lean/CriticalDepth.olean.private \
    .lake/build/lib/lean/CriticalDepth.olean.server
  cat "$proof_out/entry-point.log"
  exit "$proof_status"
fi
for proof_artifact in "$proof_artifacts/CriticalDepth.olean" \
    "$proof_artifacts/CriticalDepth.olean.private" "$proof_artifacts/CriticalDepth.olean.server"; do
  if [ -f "$proof_artifact" ]; then
    sha256sum "$proof_artifact" >> "$proof_out/project-artifacts.sha256"
  fi
done
sha256sum -c "$proof_out/sources-before.sha256" > "$proof_out/source-binding-check.txt"
sha256sum -c "$proof_out/project-artifacts.sha256" > "$proof_out/artifact-binding-check.txt"
find CriticalDepth -type f -name '*.lean' -print | \
  sed -e 's#^CriticalDepth/##' -e 's#/#.#g' -e 's#\.lean$##' | sort \
  > "$proof_out/final-modules.txt"
cmp "$proof_out/final-modules.txt" "$proof_out/scheduled-modules.txt"
sed -n 's/^.*AUDIT_MODULE \(CriticalDepth\.[A-Za-z0-9_]*\)$/\1/p' "$proof_out/Audit.log" | sort \
  > "$proof_out/audited-modules.txt"
printf 'CriticalDepth.%s\n' $proof_modules | sed '/^CriticalDepth\.Audit$/d' | sort \
  > "$proof_out/expected-audited-modules.txt"
cmp "$proof_out/audited-modules.txt" "$proof_out/expected-audited-modules.txt"
grep -F 'CRITICAL_DEPTH_AUDIT_PASSED' "$proof_out/Audit.log"
printf 'All project modules, examples and recursive audit passed. Logs: %s\n' "$proof_out"
