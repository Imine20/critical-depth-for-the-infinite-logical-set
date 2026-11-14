import FaultLowerCriterion
import FaultOnSiteSupport
import FaultEnvelopeScaling
import ShorPhysicalChecks
import PauliGroup
import FaultDepthOne
import ShorPhysicalCode
import Q37ParityPolynomial
import FaultHistoryNormalization
import CSSQuadraticPhase
import CSSMonomial
import CSSPhaseOverlap
import ShorNativeFanout
import ShorPhysicalZChecks
import ShorNativeSitePermutation
import Q37MaskCertificate
import FaultHistoryExperimentNormalization
import ShorStabilizer
import ShorNativeParallelFanout
import FaultOnsetConsequence
import ShorPauliMasks
import ShorNativeParentLayer
import ShorDistanceDetection
import ShorPhysicalXLogical
import ShorNativeTransitionArity
import ShorExactDistance
import ShorNativeSaturation
import ShorNativeTransition
import ShorNativeLayerAction
import CSSDisjointEquations

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`FaultLowerCriterion, `FaultOnSiteSupport, `FaultEnvelopeScaling, `ShorPhysicalChecks, `PauliGroup, `FaultDepthOne, `ShorPhysicalCode, `Q37ParityPolynomial, `FaultHistoryNormalization, `CSSQuadraticPhase, `CSSMonomial, `CSSPhaseOverlap, `ShorNativeFanout, `ShorPhysicalZChecks, `ShorNativeSitePermutation, `Q37MaskCertificate, `FaultHistoryExperimentNormalization, `ShorStabilizer, `ShorNativeParallelFanout, `FaultOnsetConsequence, `ShorPauliMasks, `ShorNativeParentLayer, `ShorDistanceDetection, `ShorPhysicalXLogical, `ShorNativeTransitionArity, `ShorExactDistance, `ShorNativeSaturation, `ShorNativeTransition, `ShorNativeLayerAction, `CSSDisjointEquations]
  let mut count : Nat := 0
  for mod in modules do
    let some idx := env.header.moduleNames.idxOf? mod
      | throwError "Missing imported module {mod}"
    let some data := env.header.moduleData[idx]?
      | throwError "Missing declaration table for {mod}"
    if data.constants.isEmpty then
      throwError "Empty declaration table for {mod}"
    let mut localCount : Nat := 0
    for info in data.constants do
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom {info.name}"
      let axioms ← collectAxioms info.name
      let forbidden := axioms.filter fun axiomName => !allowed.contains axiomName
      unless forbidden.isEmpty do
        throwError "{info.name} depends on forbidden axioms {forbidden}"
      localCount := localCount + 1
      if let .thmInfo _ := info then
        logInfo m!"RECURSIVE_AXIOMS {info.name}: {axioms}"
    count := count + localCount
    logInfo m!"MODULE_AUDIT_PASSED {mod} declarations={localCount}"
  logInfo m!"FURTHER_SUPPLEMENT_AUDIT_PASSED declarations={count} modules={modules.size}"
