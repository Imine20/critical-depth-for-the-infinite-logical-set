import CriticalDepth.MainResults
import CriticalDepth.FourQubitStabilizer

/-!
# Closed calls of the manuscript results for the explicit four-qubit code

Every code, stabilizer, and distance premise is supplied by the concrete
example. The only parameter below is the arbitrary finite unary depth budget.
These declarations are candidates until their recorded build and recursive
axiom audit succeed.
-/

namespace CriticalDepth.Manuscript.MainExamples

theorem fourQubit_binary_criticalDepth : Arithmetic.criticalDepth 2 2 = 1 := by
  have hm : Nat.clog 2 2 = 1 :=
    Arithmetic.clog_eq_one_of_distance_le_arity 2 2 (by decide) (by decide) (by decide)
  norm_num [Arithmetic.criticalDepth, hm]

/-- A direct call of the original at-most-depth finiteness and non-density result. -/
theorem fourQubit_binary_depthZero_finite_nondense :
    (arbitraryLogicalImageAtMost FourQubit.code 2 0).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 4) ⁻¹'
        arbitraryLogicalImageAtMost FourQubit.code 2 0) := by
  apply theoremOneAtMost_proved 4 4 1 2 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.detectsBelow_two 2 0
  left
  constructor
  · decide
  · rw [fourQubit_binary_criticalDepth]
    decide

/-- Unary gates have a finite logical image at every finite total-depth budget. -/
theorem fourQubit_unary_budget_finite_nondense (h : ℕ) :
    (arbitraryLogicalImageAtMost FourQubit.code 1 h).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 4) ⁻¹'
        arbitraryLogicalImageAtMost FourQubit.code 1 h) := by
  exact theoremOneAtMost_proved 4 4 1 2 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.detectsBelow_two 1 h (Or.inr rfl)

/-- A direct call of Theorem 2 with its original common total-depth budget. -/
theorem fourQubit_binary_critical_subgroup :
    hInfinityAtMost FourQubit.code 2 = 1 ∧
      HasContinuousLogicalSubgroupAtMost FourQubit.code 2 1 := by
  have hh := theoremTwoAtMost_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.isStabilizer FourQubit.hasActualDistance_two
  simpa [fourQubit_binary_criticalDepth] using hh

/-- The corresponding exact-depth statement also calls the closed original target. -/
theorem fourQubit_binary_exactDepth_critical_subgroup :
    hInfinity FourQubit.code 2 = 1 ∧
      HasContinuousLogicalSubgroup FourQubit.code 2 1 := by
  have hh := theoremTwo_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.isStabilizer FourQubit.hasActualDistance_two
  simpa [fourQubit_binary_criticalDepth] using hh

/-- The actual infinite image at budget one, obtained from the constructed family. -/
theorem fourQubit_binary_budgetOne_infinite :
    (arbitraryLogicalImageAtMost FourQubit.code 2 1).Infinite := by
  have hh := (stabilizer_critical_logical_image (k := 2) (d := 2) (q := 2) FourQubit.code
    (by decide) (by decide) (by decide)
    FourQubit.isStabilizer FourQubit.hasActualDistance_two).1
  rw [fourQubit_binary_criticalDepth] at hh
  exact hh.mono (logicalImage_subset_atMost FourQubit.code 2 1 1 (le_refl _))

end CriticalDepth.Manuscript.MainExamples
