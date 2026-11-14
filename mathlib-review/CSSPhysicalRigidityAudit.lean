import CSSCodeOrthogonality
import CSSCodeCosets
import CSSCodeCosetRange
import CSSCodeEncoding
import CSSCodeStabilizer
import CSSCodeDimension
import CSSCodeDistance
import CSSDegenerateDistance
import CSSCodePauliChecks
import CSSCodePauliMasks
import CSSCodeStabilizerElements
import CSSCodeNormalizerAction
import CSSRigidityCheckSpaces
import CSSPhysicalCheckClassification
import CSSConcreteMonomial
import CSSPhaseGraph
import CSSPhaseRigidity
import CSSPauliMonomial
import CSSCircuitRigidity
import CSSUpperSaturation
import CSSBinaryMonomial
import CSSComputationalMonomial
import CSSIsolatingShifts
import CSSMixedConstancy
import CSSMonomialCosets
import CSSMonomialLocality
import CSSMonomialPhaseLocality
import CSSPauliRestriction
import CSSPhysicalMonomial
import CSSPhysicalRangePreservation
import CSSShortDualTests
import CSSZCentralizer
import CSSZConjugation

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`CSSCodeOrthogonality, `CSSCodeCosets, `CSSCodeCosetRange, `CSSCodeEncoding, `CSSCodeStabilizer, `CSSCodeDimension, `CSSCodeDistance, `CSSDegenerateDistance, `CSSCodePauliChecks, `CSSCodePauliMasks, `CSSCodeStabilizerElements, `CSSCodeNormalizerAction, `CSSRigidityCheckSpaces, `CSSPhysicalCheckClassification, `CSSConcreteMonomial, `CSSPhaseGraph, `CSSPhaseRigidity, `CSSPauliMonomial, `CSSCircuitRigidity, `CSSUpperSaturation, `CSSBinaryMonomial, `CSSComputationalMonomial, `CSSIsolatingShifts, `CSSMixedConstancy, `CSSMonomialCosets, `CSSMonomialLocality, `CSSMonomialPhaseLocality, `CSSPauliRestriction, `CSSPhysicalMonomial, `CSSPhysicalRangePreservation, `CSSShortDualTests, `CSSZCentralizer, `CSSZConjugation]
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
  logInfo m!"CSS_PHYSICAL_RIGIDITY_AUDIT_PASSED declarations={count} modules={modules.size}"
