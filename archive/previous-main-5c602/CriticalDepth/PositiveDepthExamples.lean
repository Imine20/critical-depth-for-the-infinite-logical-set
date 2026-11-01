import CriticalDepth.PositiveDepth
import CriticalDepth.MainExamples

/-!
# Closed examples for the current manuscript's positive-depth minimum

The four-qubit declarations supply every code, stabilizer, and distance
premise from the concrete encoding. Their comparison of positive and
nonnegative minima uses its finite depth-zero budget image. The labeled
five-site application schema retains the code and detection hypotheses as
parameters.
-/

namespace CriticalDepth.Manuscript.PositiveDepthExamples

/-- A generic current-Theorem-1 application schema at a positive depth budget.
The encoding and its original distance-detection hypothesis are parameters;
this declaration does not construct a five-qubit code. -/
theorem fiveSite_distanceThree_positiveBudget_schema
    (C : Code 5 (fun _ => 2) 2 1) (hdetect : DetectsBelow C 3) :
    (arbitraryLogicalImageAtMost C 2 1).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 2) ⁻¹'
        arbitraryLogicalImageAtMost C 2 1) := by
  have hcritical : Arithmetic.criticalDepth 2 3 = 3 := by decide
  exact theoremOnePositive_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide) C hdetect 2 1
    (by decide) (by decide) (by rw [hcritical]; decide)

/-- A direct call of the current manuscript's positive-minimum Theorem 2. -/
theorem fourQubit_positive_critical_subgroup :
    hInfinityPositiveAtMost FourQubit.code 2 = 1 ∧
      HasContinuousLogicalSubgroupAtMost FourQubit.code 2 1 := by
  have hh := theoremTwoPositive_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.isStabilizer FourQubit.hasActualDistance_two
  simpa [MainExamples.fourQubit_binary_criticalDepth] using hh

/-- The actual zero-budget image supplies the only premise of the minimum comparison. -/
theorem fourQubit_positive_eq_nonnegative :
    hInfinityPositiveAtMost FourQubit.code 2 = hInfinityAtMost FourQubit.code 2 := by
  exact hInfinityPositiveAtMost_eq_hInfinityAtMost FourQubit.code 2
    MainExamples.fourQubit_binary_depthZero_finite_nondense.1

theorem fourQubit_positive_minimum_one : hInfinityPositiveAtMost FourQubit.code 2 = 1 :=
  fourQubit_positive_critical_subgroup.1

theorem fourQubit_positive_continuous_subgroup :
    HasContinuousLogicalSubgroupAtMost FourQubit.code 2 1 :=
  fourQubit_positive_critical_subgroup.2

end CriticalDepth.Manuscript.PositiveDepthExamples
