import CriticalDepthMathlib

/-!
# Two-level Givens blocks

The block removes a selected column entry with no loss of its relative
phase. These identities cover the nonzero pivot branch of exact elimination.
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix
open scoped BigOperators

noncomputable section

/-- The norm of the two column entries on which the elimination acts. -/
def givensRadius (a b : ℂ) : ℝ := Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2)

theorem givensRadius_sq (a b : ℂ) : givensRadius a b ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem givensRadius_eq_zero_iff (a b : ℂ) : givensRadius a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hs := givensRadius_sq a b
    rw [h, zero_pow (by decide)] at hs
    have ha : ‖a‖ = 0 := by nlinarith [sq_nonneg ‖b‖]
    have hb : ‖b‖ = 0 := by nlinarith [sq_nonneg ‖a‖]
    exact ⟨norm_eq_zero.mp ha, norm_eq_zero.mp hb⟩
  · rintro ⟨rfl, rfl⟩
    simp [givensRadius]

/-- The exact complex Givens rotation on the pivot and target rows. -/
def givensBlock (a b : ℂ) : Operator (Fin 2) :=
  ((givensRadius a b : ℂ)⁻¹) • !![star a, star b; -b, a]

private theorem givensRadius_sq_complex (a b : ℂ) :
    (givensRadius a b : ℂ) ^ 2 = a * starRingEnd ℂ a + b * starRingEnd ℂ b := by
  simp only [← Complex.ofReal_pow, Complex.mul_conj']
  exact_mod_cast givensRadius_sq a b

theorem givensBlock_mulVec (a b : ℂ) (hr : givensRadius a b ≠ 0) :
    givensBlock a b *ᵥ ![a, b] = ![(givensRadius a b : ℂ), 0] := by
  have hrC : (givensRadius a b : ℂ) ≠ 0 := by exact_mod_cast hr
  funext i
  fin_cases i <;>
    simp [givensBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  · have h := givensRadius_sq_complex a b
    field_simp [hrC]
    linear_combination -h
  · ring

theorem givensBlock_isUnitary (a b : ℂ) (hr : givensRadius a b ≠ 0) :
    IsUnitary (givensBlock a b) := by
  have hRadius := givensRadius_sq_complex a b
  have hrC : (givensRadius a b : ℂ) ≠ 0 := by exact_mod_cast hr
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [givensBlock, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, star_mul, star_inv₀] <;>
    field_simp [hrC] <;> first | solve_by_elim | linear_combination -hRadius | ring

#print axioms givensBlock_mulVec
#print axioms givensBlock_isUnitary

end

end CriticalDepth.Manuscript20261114
