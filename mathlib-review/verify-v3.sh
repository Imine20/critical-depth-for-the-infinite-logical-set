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
modules='CriticalDepthMathlib SourceConsumer EncodedInverse Manuscript20261114Baseline GenerationThresholds RealAlgebraicImage BarePauliRotations FaultDepthArithmetic FaultProbability FaultHistoryLoss FaultChoiBound PauliSyndromeOptimization FaultCircuitSupport OrthogonalRecovery RecoveryCrossTerms Q37BinaryData Q37DistanceData Manuscript20261114Audit RealAlgebraicCurves CircuitRealPolynomial UnitaryAdjointSpan DenseUnitaryAdjointSpan UnitaryCurveProducts NativeLogicalCurves ExactGeneration ExactGenerationAudit IndependentFaultHistories FaultExponent KnillLaflammeGram FaultEntanglementFidelity FaultAmbiguity EncodedFaultRecovery FaultHistoryGeometry FaultKrausCompactness FaultKrausCompression FaultStabilizerTrace MidpointFaultWitness FaultUpperWitness FaultCPTPRepresentation FaultCPTPOptimality FaultLawIndependence FaultNativeModel FaultNativeCeiling FaultShorSaturation FaultShorEncoding FaultShorSchedule FaultShorScheduleIteration CSSCheckSpaces CSSPermutationRigidity CSSPhaseDifferences SupplementSynthesis ContinuationAudit FaultAverageInfidelity FaultIdealAction BinaryPermutationUnitary ShorPermutationAction FaultSupportPreserving FinalSupplementAudit FaultLowerCriterion FaultOnSiteSupport FaultEnvelopeScaling ShorPhysicalChecks PauliGroup FaultDepthOne ShorPhysicalCode Q37ParityPolynomial FaultHistoryNormalization CSSQuadraticPhase CSSMonomial CSSPhaseOverlap ShorNativeFanout ShorPhysicalZChecks ShorNativeSitePermutation Q37MaskCertificate FaultHistoryExperimentNormalization ShorStabilizer ShorNativeParallelFanout FaultOnsetConsequence ShorPauliMasks ShorNativeParentLayer ShorDistanceDetection ShorPhysicalXLogical ShorNativeTransitionArity ShorExactDistance ShorNativeSaturation ShorNativeTransition ShorNativeLayerAction CSSDisjointEquations FurtherSupplementAudit ShorCyclePacking ShorGroupLayout ShorCycleAction ShorIndexedSchedule ShorIndexedScheduleLift ShorIndexedScheduleMasks ShorIndexedScheduleColumn ShorFaultWitness ShorFaultWitnessAmbiguity ShorRowAction ShorRowActionColumns ShorBoundaryCircuit ShorBoundaryRows ShorGroupedCircuit ShorGroupedAction ShorDepthOneWitness ShorMultilayerSaturation ShorLowerSaturation ShorSaturationConsumer ShorSaturationAudit CSSCodeOrthogonality CSSCodeCosets CSSCodeCosetRange CSSCodeEncoding CSSCodeStabilizer CSSCodeDimension CSSCodeDistance CSSDegenerateDistance CSSCodePauliChecks CSSCodePauliMasks CSSCodeStabilizerElements CSSCodeNormalizerAction CSSRigidityCheckSpaces CSSPhysicalCheckClassification CSSConcreteMonomial CSSPhaseGraph CSSPhaseRigidity CSSPauliMonomial CSSCircuitRigidity CSSUpperSaturation CSSBinaryMonomial CSSComputationalMonomial CSSIsolatingShifts CSSMixedConstancy CSSMonomialCosets CSSMonomialLocality CSSMonomialPhaseLocality CSSPauliRestriction CSSPhysicalMonomial CSSPhysicalRangePreservation CSSShortDualTests CSSZCentralizer CSSZConjugation CSSPhysicalRigidityAudit BaconShorBinaryGeometry BaconShorCoordinates BaconShorGaugeTrace BaconShorRealLog BaconShorSubsystemEncoding CSSFourierCharacterSums FaultChannelEffects FaultDiamondEffects FaultDiamondFrame FaultHaarSphere FaultPauliSyndromeChannel FaultStabilizerSyndrome FaultVariationalTrace OneQubitEuler Q37BlockPhasePolynomial Q37NativeParityLayer ReducedCircuitPresentation BaconShorAdjacentGauges BaconShorBareAxes BaconShorFixedSpace BaconShorGaugeCoordinates FaultBellEffect FaultDiamondHistories FaultDiamondIdealAction FaultDiamondOptimality FaultDiamondTail FaultDiamondVariational FaultHaarRealMoments FaultStabilizerLogicalTrace FaultTraceNorm OneQubitBareSynthesis Q37ConjugatedParityLayer Q37NativeBlocks Q37PhaseBridge Q37PhysicalParityLayers Q37SupportSplits ReducedCircuitInverses ReducedCircuitIsomorphism BaconShorGaugeActions FaultHaarComplexMoment FaultStabilizerLogicalBasis FaultStabilizerPauliChannel Q37CheckSpaces Q37DirectPhaseCertificate Q37PhaseCoefficientWords Q37SignatureBits ReducedCircuitFiniteImage BaconShorDressedDistance BaconShorShortTrace BaconShorThresholdUpper BaconShorXAxisNormalizer ErrorMeasuresFoundationAudit Q37CanonicalEncoding Q37CanonicalLogicalPauli Q37PackedSignatures ReducedCircuitAudit BaconShorAspectRatio BaconShorProposition Q37ActualDistance Q37CanonicalDistance Q37DataAudit BaconShorAudit'
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
grep -F EXACT_GENERATION_AUDIT_PASSED "$out/ExactGenerationAudit.log"
grep -F CONTINUATION_AUDIT_PASSED "$out/ContinuationAudit.log"
grep -F SUPPLEMENT_AUDIT_PASSED "$out/FinalSupplementAudit.log"
grep -F FURTHER_SUPPLEMENT_AUDIT_PASSED "$out/FurtherSupplementAudit.log"
grep -F SHOR_SATURATION_AUDIT_PASSED "$out/ShorSaturationAudit.log"
grep -F CSS_PHYSICAL_RIGIDITY_AUDIT_PASSED "$out/CSSPhysicalRigidityAudit.log"
grep -F BACON_SHOR_AUDIT_PASSED "$out/BaconShorAudit.log"
grep -F REDUCED_CIRCUIT_AUDIT_PASSED "$out/ReducedCircuitAudit.log"
grep -F Q37_DATA_AUDIT_PASSED "$out/Q37DataAudit.log"
grep -F ERROR_MEASURES_FOUNDATION_AUDIT_PASSED "$out/ErrorMeasuresFoundationAudit.log"
if grep -E 'uses .sorry.|sorryAx|depends on axioms:.*native_decide' "$out"/*.log; then
  exit 1
fi
