import BinaryPauliMasks
import BinarySymplecticElimination
import ConnectedPauliFrameSynthesis
import ExactConditionalPhase
import ExactConditionalRotation
import ExactConnectedCNOT
import ExactControlledTarget
import ExactControlledWord
import ExactControlProjector
import ExactControlProjectorProduct
import ExactCZCNOTSwap
import ExactGivensBlock
import ExactGivensCompiler
import ExactGivensElimination
import ExactGivensNativeWord
import ExactGivensStep
import ExactGraphCNOTRouting
import ExactGraphEdgeOperator
import ExactGraphSWAP
import ExactGrayRouting
import ExactGrayTwoLevel
import ExactPauliCliffordParity
import ExactPauliParityCircuit
import ExactSerialSynthesis
import ExactTwoLevelWord
import LogicalFrameRotationTransport
import LogicalPauliOrbit
import LogicalPauliOrbitBasis
import LogicalPauliVacuum
import MatrixUnitaryConnected
import OneQubitBareSynthesis
import OneQubitEuler
import StabilizerCosetSelection
import StabilizerFrameSynthesis
import StabilizerLogicalFrame
import StabilizerMinUnphased
import StabilizerPauliFrame
import StabilizerPauliFrameAction
import SynthesisFiniteWords
import TensorPauliConjugation
import TensorPauliConnectedFrame
import TensorPauliTangents
import NativeScalarPhase
import ExactGivensNativeTarget
import StabilizerNativeGivens

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`BinaryPauliMasks, `BinarySymplecticElimination, `ConnectedPauliFrameSynthesis, `ExactConditionalPhase, `ExactConditionalRotation, `ExactConnectedCNOT, `ExactControlledTarget, `ExactControlledWord, `ExactControlProjector, `ExactControlProjectorProduct, `ExactCZCNOTSwap, `ExactGivensBlock, `ExactGivensCompiler, `ExactGivensElimination, `ExactGivensNativeWord, `ExactGivensStep, `ExactGraphCNOTRouting, `ExactGraphEdgeOperator, `ExactGraphSWAP, `ExactGrayRouting, `ExactGrayTwoLevel, `ExactPauliCliffordParity, `ExactPauliParityCircuit, `ExactSerialSynthesis, `ExactTwoLevelWord, `LogicalFrameRotationTransport, `LogicalPauliOrbit, `LogicalPauliOrbitBasis, `LogicalPauliVacuum, `MatrixUnitaryConnected, `OneQubitBareSynthesis, `OneQubitEuler, `StabilizerCosetSelection, `StabilizerFrameSynthesis, `StabilizerLogicalFrame, `StabilizerMinUnphased, `StabilizerPauliFrame, `StabilizerPauliFrameAction, `SynthesisFiniteWords, `TensorPauliConjugation, `TensorPauliConnectedFrame, `TensorPauliTangents, `NativeScalarPhase, `ExactGivensNativeTarget, `StabilizerNativeGivens]
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
  logInfo m!"CONSTRUCTIVE_SYNTHESIS_AUDIT_PASSED declarations={count} modules={modules.size}"
