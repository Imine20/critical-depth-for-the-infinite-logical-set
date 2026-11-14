import Manuscript20261114Baseline
import GenerationThresholds
import RealAlgebraicImage
import BarePauliRotations
import EncodedInverse
import FaultDepthArithmetic
import FaultCircuitSupport
import FaultProbability
import FaultHistoryLoss
import FaultChoiBound
import PauliSyndromeOptimization
import OrthogonalRecovery
import RecoveryCrossTerms
import Q37BinaryData
import Q37DistanceData

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`Manuscript20261114Baseline, `GenerationThresholds, `RealAlgebraicImage,
    `BarePauliRotations, `EncodedInverse, `FaultDepthArithmetic, `FaultCircuitSupport,
    `FaultProbability, `FaultHistoryLoss, `FaultChoiBound, `PauliSyndromeOptimization,
    `OrthogonalRecovery, `RecoveryCrossTerms, `Q37BinaryData, `Q37DistanceData]
  let moduleNames := env.header.moduleNames
  let mut count : Nat := 0
  for mod in modules do
    let some idx := moduleNames.idxOf? mod
      | throwError "V3 audit omitted module {mod}"
    let some data := env.header.moduleData[idx]?
      | throwError "Missing imported declaration table for {mod}"
    unless !data.constants.isEmpty do
      throwError "Empty imported declaration table for {mod}"
    for info in data.constants do
      let name := info.name
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom {name}"
      let axioms ← collectAxioms name
      let forbidden := axioms.filter fun axiomName => !allowed.contains axiomName
      unless forbidden.isEmpty do
        throwError "{name} depends on forbidden axioms {forbidden}"
      count := count + 1
      if let .thmInfo _ := info then
        logInfo m!"V3_RECURSIVE_AXIOMS {name}: {axioms}"
        unless name.isInternal do
          liftTermElabM do
            let type ← Meta.ppExpr info.type
            logInfo m!"V3_TYPE {name}\n{type}"
  logInfo m!"V3_RECURSIVE_AUDIT_PASSED declarations={count} modules={modules.size}"
