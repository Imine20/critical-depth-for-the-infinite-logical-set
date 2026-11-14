import BinaryPermutationDiagonal
import CliffordTClosureCriterion
import CliffordTDenseCircle
import CliffordTDensity
import CliffordTIrrationalAngle
import CliffordTMixedAxis
import CliffordTTangents
import CliffordTWords
import Q37CliffordTWords
import Q37ConcreteThreshold
import Q37HadamardFourier
import Q37LogicalNativeGates
import Q37NamedRotation
import Q37PhysicalCompression
import Q37PhysicalPhases
import Q37Threshold
import NamedBareRotation
import CliffordTNativeThreshold

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`BinaryPermutationDiagonal, `CliffordTClosureCriterion, `CliffordTDenseCircle, `CliffordTDensity, `CliffordTIrrationalAngle, `CliffordTMixedAxis, `CliffordTTangents, `CliffordTWords, `Q37CliffordTWords, `Q37ConcreteThreshold, `Q37HadamardFourier, `Q37LogicalNativeGates, `Q37NamedRotation, `Q37PhysicalCompression, `Q37PhysicalPhases, `Q37Threshold, `NamedBareRotation, `CliffordTNativeThreshold]
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
  logInfo m!"Q37_GATES_AUDIT_PASSED declarations={count} modules={modules.size}"
