import CriticalDepth
import CriticalDepth.MainExamples

/-! A standalone client of the public entry point and the exact-depth helpers.
The original common-budget calls are in CriticalDepth.MainExamples. -/

namespace CriticalDepth.Verification.StandaloneConsumer

open CriticalDepth.Manuscript

theorem exact_finiteness_call : (logicalImage FourQubit.code 2 0).Finite := by
  apply theoremOne_proved 4 4 1 2 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.detectsBelow_two 2 0
  exact Or.inl ⟨by decide, by rw [MainExamples.fourQubit_binary_criticalDepth]; decide⟩

theorem exact_nondensity_call :
    ¬ Dense (projectiveUnitaryToOperator (Fin 4) ⁻¹' logicalImage FourQubit.code 2 0) := by
  apply theoremOne_nondense 4 4 1 2 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.detectsBelow_two 2 0
  exact Or.inl ⟨by decide, by rw [MainExamples.fourQubit_binary_criticalDepth]; decide⟩

#print axioms exact_finiteness_call
#print axioms exact_nondensity_call

end CriticalDepth.Verification.StandaloneConsumer
