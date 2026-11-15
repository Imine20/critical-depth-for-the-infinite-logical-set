import FaultFirstBadOrderLower
import FaultFirstBadOrderUpper
import FaultPointwiseAmbiguity
import FaultFirstBadOrder
import FaultPaperFixedCircuit
import FaultPaperSaturationWitness
import UpdateBranchConsumer

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`FaultFirstBadOrderLower, `FaultFirstBadOrderUpper, `FaultPointwiseAmbiguity, `FaultFirstBadOrder, `FaultPaperFixedCircuit, `FaultPaperSaturationWitness, `UpdateBranchConsumer]
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
  logInfo m!"UPDATE_BRANCH_AUDIT_PASSED declarations={count} modules={modules.size}"

#check @CriticalDepth.ReviewV2.nativeTheoremOne_proved
#print axioms CriticalDepth.ReviewV2.nativeTheoremOne_proved
#check @CriticalDepth.ReviewV2.standardTheoremTwo_proved
#print axioms CriticalDepth.ReviewV2.standardTheoremTwo_proved
#check @CriticalDepth.ReviewV2.nativeExactDepth_eq_max
#print axioms CriticalDepth.ReviewV2.nativeExactDepth_eq_max
#check @CriticalDepth.Manuscript20261114.sharpFaultSuppression_bounds_allMetrics
#print axioms CriticalDepth.Manuscript20261114.sharpFaultSuppression_bounds_allMetrics
#check @CriticalDepth.Manuscript20261114.sharpFaultSuppression_lower_paper_witness_allMetrics
#print axioms CriticalDepth.Manuscript20261114.sharpFaultSuppression_lower_paper_witness_allMetrics
#check @CriticalDepth.Manuscript20261114.sharpFaultSuppression_upper_paper_witness_allMetrics
#print axioms CriticalDepth.Manuscript20261114.sharpFaultSuppression_upper_paper_witness_allMetrics
#check @CriticalDepth.FaultFirstBadOrder.historyErrors_firstUncorrectableOrder
#print axioms CriticalDepth.FaultFirstBadOrder.historyErrors_firstUncorrectableOrder
#check @CriticalDepth.FaultFirstBadOrder.paperCircuitErrorExponents_eq_firstUncorrectableOrder
#print axioms CriticalDepth.FaultFirstBadOrder.paperCircuitErrorExponents_eq_firstUncorrectableOrder
#check @CriticalDepth.FaultPointwiseAmbiguity.minWeight_le_optimalCPTPInfidelity_of_ambiguous_pair
#print axioms CriticalDepth.FaultPointwiseAmbiguity.minWeight_le_optimalCPTPInfidelity_of_ambiguous_pair

#print CriticalDepth.ReviewV2.NativeTheoremOne
#print CriticalDepth.ReviewV2.StandardTheoremTwo
