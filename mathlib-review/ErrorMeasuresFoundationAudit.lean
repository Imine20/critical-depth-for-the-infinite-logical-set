import FaultChannelEffects
import FaultDiamondEffects
import FaultVariationalTrace
import FaultTraceNorm
import FaultDiamondVariational
import FaultBellEffect
import FaultDiamondFrame
import FaultDiamondHistories
import FaultDiamondTail
import FaultDiamondOptimality
import FaultDiamondIdealAction
import FaultStabilizerSyndrome
import FaultPauliSyndromeChannel
import FaultStabilizerLogicalTrace
import FaultStabilizerLogicalBasis
import FaultStabilizerPauliChannel
import FaultHaarSphere
import FaultHaarRealMoments
import FaultHaarComplexMoment
import FaultCPTPRepresentation
import FaultCPTPOptimality
import FaultHistoryExperimentNormalization

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`FaultChannelEffects, `FaultDiamondEffects, `FaultVariationalTrace, `FaultTraceNorm, `FaultDiamondVariational, `FaultBellEffect, `FaultDiamondFrame, `FaultDiamondHistories, `FaultDiamondTail, `FaultDiamondOptimality, `FaultDiamondIdealAction, `FaultStabilizerSyndrome, `FaultPauliSyndromeChannel, `FaultStabilizerLogicalTrace, `FaultStabilizerLogicalBasis, `FaultStabilizerPauliChannel, `FaultHaarSphere, `FaultHaarRealMoments, `FaultHaarComplexMoment, `FaultCPTPRepresentation, `FaultCPTPOptimality, `FaultHistoryExperimentNormalization]
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
  logInfo m!"ERROR_MEASURES_FOUNDATION_AUDIT_PASSED declarations={count} modules={modules.size}"
