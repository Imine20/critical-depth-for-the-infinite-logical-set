import FaultDiamondCSSSaturation
import FaultDiamondExponent
import FaultDiamondNormalization
import FaultDiamondPaperMetric
import FaultDiamondTraceInputs
import FaultHaarChannelFidelity
import FaultHaarChannelGeometry
import FaultHaarNativeModel
import FaultHaarOptimality
import FaultHaarSaturation
import FaultNativePauliDecoding
import FaultUpperOnsetWitness
import MidpointEvenPauliCircuit
import MidpointExactFaultWitness
import MidpointLogicalCeiling
import MidpointNativeHistories
import MidpointPauliCircuit
import NativeMiddlePauliHistory
import SharpFaultSuppression
import ShorOnset
import FaultChannelNormalization
import ShorFaultWitnessAmbiguity
import FaultHaarShor
import SingleFaultDetectability
import FaultSharpnessAllMetrics
import FaultOnsetScaling
import FaultLocalStochasticRecovery
import FaultLocalStochasticPaper

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`FaultDiamondCSSSaturation, `FaultDiamondExponent, `FaultDiamondNormalization, `FaultDiamondPaperMetric, `FaultDiamondTraceInputs, `FaultHaarChannelFidelity, `FaultHaarChannelGeometry, `FaultHaarNativeModel, `FaultHaarOptimality, `FaultHaarSaturation, `FaultNativePauliDecoding, `FaultUpperOnsetWitness, `MidpointEvenPauliCircuit, `MidpointExactFaultWitness, `MidpointLogicalCeiling, `MidpointNativeHistories, `MidpointPauliCircuit, `NativeMiddlePauliHistory, `SharpFaultSuppression, `ShorOnset, `FaultChannelNormalization, `ShorFaultWitnessAmbiguity, `FaultHaarShor, `SingleFaultDetectability, `FaultSharpnessAllMetrics, `FaultOnsetScaling, `FaultLocalStochasticRecovery, `FaultLocalStochasticPaper]
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
  logInfo m!"FAULT_SHARPNESS_AUDIT_PASSED declarations={count} modules={modules.size}"
