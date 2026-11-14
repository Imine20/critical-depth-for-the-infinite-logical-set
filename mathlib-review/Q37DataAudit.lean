import Q37CheckSpaces
import Q37SupportSplits
import Q37SignatureBits
import Q37PackedSignatures
import Q37ActualDistance
import Q37CanonicalEncoding
import Q37CanonicalLogicalPauli
import Q37CanonicalDistance
import Q37PhaseCoefficientWords
import Q37DirectPhaseCertificate
import Q37BlockPhasePolynomial
import Q37NativeParityLayer
import Q37ConjugatedParityLayer
import Q37NativeBlocks
import Q37PhaseBridge
import Q37PhysicalParityLayers
import CSSFourierCharacterSums

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let modules := #[`Q37CheckSpaces, `Q37SupportSplits, `Q37SignatureBits, `Q37PackedSignatures, `Q37ActualDistance, `Q37CanonicalEncoding, `Q37CanonicalLogicalPauli, `Q37CanonicalDistance, `Q37PhaseCoefficientWords, `Q37DirectPhaseCertificate, `Q37BlockPhasePolynomial, `Q37NativeParityLayer, `Q37ConjugatedParityLayer, `Q37NativeBlocks, `Q37PhaseBridge, `Q37PhysicalParityLayers, `CSSFourierCharacterSums]
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
  logInfo m!"Q37_DATA_AUDIT_PASSED declarations={count} modules={modules.size}"
