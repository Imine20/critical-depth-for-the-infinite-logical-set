import ExactControlProjector

/-!
# The factored expression of a conditional control projector
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix
open scoped BigOperators

noncomputable section

variable {k : ℕ}

/-- A control projector equals the product of the on-site signed-Z factors
scaled by `2⁻¹` for every selected bit. The factors are diagonal, so the
finite-set product of their eigenvalue functions is well defined. -/
theorem controlProjector_eq_factored_diagonal (B : Finset (Fin k)) (y : QubitBasis k) :
    controlProjector B y =
      (2 : ℂ)⁻¹ ^ B.card • Matrix.diagonal
        (∏ i ∈ B, fun x => 1 + logicalBitSign (y i) * logicalBitSign (x i)) := by
  classical
  rw [controlProjector, ← Matrix.diagonal_smul]
  apply congrArg Matrix.diagonal
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_apply]
  by_cases h : ∀ i ∈ B, x i = y i
  · rw [controlIndicator, if_pos h]
    have hp : ∏ i ∈ B, (1 + logicalBitSign (y i) * logicalBitSign (x i)) = 2 ^ B.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl (fun i hi => ?_)
      rw [h i hi]
      generalize y i = b
      fin_cases b <;> norm_num [logicalBitSign]
    rw [hp, ← mul_pow]
    norm_num
  · rw [controlIndicator, if_neg h]
    push Not at h
    obtain ⟨i, hi, hxy⟩ := h
    have hp : ∏ j ∈ B, (1 + logicalBitSign (y j) * logicalBitSign (x j)) = 0 := by
      apply Finset.prod_eq_zero hi
      generalize ha : y i = a at hxy ⊢
      generalize hb : x i = b at hxy ⊢
      fin_cases a <;> fin_cases b <;> norm_num [logicalBitSign] at *
    rw [hp, mul_zero]

#print axioms controlProjector_eq_factored_diagonal

end

end CriticalDepth.Manuscript20261114
