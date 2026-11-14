import ShorCyclePacking
import ShorGroupLayout
import ShorCycleAction
import ShorIndexedSchedule
import ShorIndexedScheduleLift
import ShorIndexedScheduleMasks
import ShorIndexedScheduleColumn
import ShorFaultWitness
import ShorFaultWitnessAmbiguity
import ShorRowAction
import ShorRowActionColumns
import ShorBoundaryCircuit
import ShorBoundaryRows
import ShorGroupedCircuit
import ShorGroupedAction
import ShorDepthOneWitness
import ShorMultilayerSaturation
import ShorLowerSaturation
import ShorSaturationConsumer

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`ShorCyclePacking, `ShorGroupLayout, `ShorCycleAction, `ShorIndexedSchedule, `ShorIndexedScheduleLift, `ShorIndexedScheduleMasks, `ShorIndexedScheduleColumn, `ShorFaultWitness, `ShorFaultWitnessAmbiguity, `ShorRowAction, `ShorRowActionColumns, `ShorBoundaryCircuit, `ShorBoundaryRows, `ShorGroupedCircuit, `ShorGroupedAction, `ShorDepthOneWitness, `ShorMultilayerSaturation, `ShorLowerSaturation, `ShorSaturationConsumer]
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
  logInfo m!"SHOR_SATURATION_AUDIT_PASSED declarations={count} modules={modules.size}"
