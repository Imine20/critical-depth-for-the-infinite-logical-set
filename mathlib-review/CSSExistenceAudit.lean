import CSSBadWordCounts
import CSSColumnRankCounts
import CSSColumnRankFactorization
import CSSDisjointSolutionCounts
import CSSExhaustiveSelection
import CSSFiniteColumns
import CSSFiniteCounts
import CSSGeneratorFibers
import CSSLinearFibers
import CSSOrderedBasisContainment
import CSSOrderedBasisSampling
import CSSPlantedHyperplane
import CSSRandomDistanceCounts
import CSSRandomJointSample
import CSSRandomLimit
import CSSRandomLinearBound
import CSSRandomParameters
import CSSRandomProbabilityArithmetic
import CSSRandomRigidity
import CSSRandomScale
import CSSRandomShellScale
import CSSRandomSparseScale
import CSSRandomXChecks
import CSSRandomZChecks
import CSSReducedRowBasis
import CSSRestrictionFibers
import CSSSparseLinearBudget
import CSSSparseLinearEquations
import CSSSparseLinearIntertwiner
import CSSSparseLinearSample
import CSSSparseLinearUnchanged
import CSSSparseMatrixCounts
import CSSSparseSymmetricRank
import CSSSparseSymmetricSampling
import CSSSparseSymmetricUnion
import CSSUpperGap
import CSSUpperSaturationFamily
import CSSWeightBallCounts
import CSSPlantedSelection

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`CSSBadWordCounts, `CSSColumnRankCounts, `CSSColumnRankFactorization, `CSSDisjointSolutionCounts, `CSSExhaustiveSelection, `CSSFiniteColumns, `CSSFiniteCounts, `CSSGeneratorFibers, `CSSLinearFibers, `CSSOrderedBasisContainment, `CSSOrderedBasisSampling, `CSSPlantedHyperplane, `CSSRandomDistanceCounts, `CSSRandomJointSample, `CSSRandomLimit, `CSSRandomLinearBound, `CSSRandomParameters, `CSSRandomProbabilityArithmetic, `CSSRandomRigidity, `CSSRandomScale, `CSSRandomShellScale, `CSSRandomSparseScale, `CSSRandomXChecks, `CSSRandomZChecks, `CSSReducedRowBasis, `CSSRestrictionFibers, `CSSSparseLinearBudget, `CSSSparseLinearEquations, `CSSSparseLinearIntertwiner, `CSSSparseLinearSample, `CSSSparseLinearUnchanged, `CSSSparseMatrixCounts, `CSSSparseSymmetricRank, `CSSSparseSymmetricSampling, `CSSSparseSymmetricUnion, `CSSUpperGap, `CSSUpperSaturationFamily, `CSSWeightBallCounts, `CSSPlantedSelection]
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
  logInfo m!"CSS_EXISTENCE_AUDIT_PASSED declarations={count} modules={modules.size}"
