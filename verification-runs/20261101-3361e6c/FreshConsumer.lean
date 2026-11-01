import CriticalDepthMathlib

/-!
External calls to the separately compiled single-file development.
The runner must put the newly produced CriticalDepthMathlib artifact before
public dependencies and exclude earlier project artifacts.  Module names alone
cannot establish artifact freshness; the runner's hash bindings establish it.

Both main native theorems are applied to actual constructed codes.  The five
qubit calls use the proved arbitrary-operator detection property.  The four
qubit call uses its proved stabilizer and actual-distance properties.
-/

noncomputable section

namespace CriticalDepth.FreshConsumer

theorem fiveQubit_depthOne :
    (CriticalDepth.ReviewV2.nativeLogicalImage
      CriticalDepth.Manuscript.FiveQubit.encoding 2 1).Finite ∧
    ¬ Dense (CriticalDepth.ReviewV2.nativeLogicalImage
      CriticalDepth.Manuscript.FiveQubit.encoding 2 1) := by
  exact CriticalDepth.ReviewV2.nativeTheoremOne_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    CriticalDepth.Manuscript.FiveQubit.encoding
    CriticalDepth.Manuscript.FiveQubit.encoding_isometry
    CriticalDepth.Manuscript.FiveQubit.detectsBelow_three
    2 1 (by decide) (by decide) (by decide)

theorem fiveQubit_depthTwo :
    (CriticalDepth.ReviewV2.nativeLogicalImage
      CriticalDepth.Manuscript.FiveQubit.encoding 2 2).Finite ∧
    ¬ Dense (CriticalDepth.ReviewV2.nativeLogicalImage
      CriticalDepth.Manuscript.FiveQubit.encoding 2 2) := by
  exact CriticalDepth.ReviewV2.nativeTheoremOne_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    CriticalDepth.Manuscript.FiveQubit.encoding
    CriticalDepth.Manuscript.FiveQubit.encoding_isometry
    CriticalDepth.Manuscript.FiveQubit.detectsBelow_three
    2 2 (by decide) (by decide) (by decide)

theorem fourQubit_criticalDepth_and_closedCircle :
    CriticalDepth.ReviewV2.nativeCriticalDepth
      CriticalDepth.Manuscript.FourQubit.encoding 2 = (1 : ℕ∞) ∧
    ∃ S : Subgroup (CriticalDepth.ReviewV2.PU (Fin (2 ^ 2))),
      IsClosed (S : Set (CriticalDepth.ReviewV2.PU (Fin (2 ^ 2)))) ∧ S ≠ ⊥ ∧
      Nonempty (ContinuousMulEquiv Circle S) ∧
      (S : Set (CriticalDepth.ReviewV2.PU (Fin (2 ^ 2)))) ⊆
        CriticalDepth.ReviewV2.nativeLogicalImage
          CriticalDepth.Manuscript.FourQubit.encoding 2 1 := by
  have hstabilizer : CriticalDepth.ReviewV2.NativeStabilizer (k := 2)
      CriticalDepth.Manuscript.FourQubit.encoding :=
    (CriticalDepth.ReviewV2.nativeStabilizer_iff_legacy (k := 2)
      CriticalDepth.Manuscript.FourQubit.encoding
      CriticalDepth.Manuscript.FourQubit.encoding_isometry).mpr
      CriticalDepth.Manuscript.FourQubit.isStabilizer
  have hdistance : CriticalDepth.ReviewV2.NativeActualDistance
      CriticalDepth.Manuscript.FourQubit.encoding 2 :=
    (CriticalDepth.ReviewV2.nativeActualDistance_iff_legacy
      CriticalDepth.Manuscript.FourQubit.encoding
      CriticalDepth.Manuscript.FourQubit.encoding_isometry 2).mpr
      CriticalDepth.Manuscript.FourQubit.hasActualDistance_two
  have h := CriticalDepth.ReviewV2.nativeTheoremTwo_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    CriticalDepth.Manuscript.FourQubit.encoding
    CriticalDepth.Manuscript.FourQubit.encoding_isometry hstabilizer hdistance
  have hdepth : CriticalDepth.Arithmetic.criticalDepth 2 2 = 1 := by decide
  simpa only [hdepth, ENat.natCast_one] using h

#print axioms CriticalDepth.ReviewV2.nativeTheoremOne_proved
#print axioms CriticalDepth.ReviewV2.nativeTheoremTwo_proved
#print axioms CriticalDepth.FreshConsumer.fiveQubit_depthOne
#print axioms CriticalDepth.FreshConsumer.fiveQubit_depthTwo
#print axioms CriticalDepth.FreshConsumer.fourQubit_criticalDepth_and_closedCircle

end CriticalDepth.FreshConsumer

end

open Lean Meta Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let importedMains : Array Name :=
    #[`CriticalDepth.ReviewV2.nativeTheoremOne_proved,
      `CriticalDepth.ReviewV2.nativeTheoremTwo_proved]
  let calls : Array Name :=
    #[`CriticalDepth.FreshConsumer.fiveQubit_depthOne,
      `CriticalDepth.FreshConsumer.fiveQubit_depthTwo,
      `CriticalDepth.FreshConsumer.fourQubit_criticalDepth_and_closedCircle]
  unless env.header.moduleNames.contains `CriticalDepthMathlib do
    throwError "The external consumer did not import CriticalDepthMathlib"
  for name in importedMains do
    let some idx := env.getModuleIdxFor? name
      | throwError "Imported main target {name} lacks an imported-module origin"
    unless env.header.moduleNames[idx.toNat]? == some `CriticalDepthMathlib do
      throwError "Imported main target {name} comes from another module"
    logInfo m!"FRESH_CONSUMER_MAIN_ORIGIN {name} origin=CriticalDepthMathlib"
  for name in calls do
    if (env.getModuleIdxFor? name).isSome then
      throwError "Consumer call {name} is imported instead of elaborated here"
    match ← getConstInfo name with
    | .thmInfo _ => pure ()
    | _ => throwError "Consumer call {name} is not a theorem declaration"
  let mut checks : Nat := 0
  for name in importedMains ++ calls do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun a => !allowed.contains a
    let missing := allowed.filter fun a => !axioms.contains a
    unless forbidden.isEmpty && missing.isEmpty && axioms.size == 3 do
      throwError "Consumer target {name} does not recursively use exactly the standard three axioms"
    checks := checks + 1
    let names := String.intercalate ", " (axioms.toList.map Name.toString)
    logInfo m!"FRESH_CONSUMER_AXIOMS {name} [{names}]"
  unless checks == 5 do
    throwError "Expected five recursive exact-three checks, got {checks}"
  logInfo "FRESH_EXTERNAL_CONSUMER_PASSED call_count=3 imported_main_count=2 exact_three_count=5"
