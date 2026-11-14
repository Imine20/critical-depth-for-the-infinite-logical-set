import CliffordTWords

/-!
# The seven-letter projective T word in the Q37 generator D
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.Manuscript20261114.OneQubitEuler

noncomputable section

private theorem projectiveZ_nsmul (m : ℕ) (t : ℝ) :
    projectiveZ ((m : ℝ) * t) = (projectiveZ t) ^ m := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    unfold projectiveZ projectiveRotation
    rw [← map_one (projectiveMk (Fin 2))]
    apply congrArg (projectiveMk (Fin 2))
    apply Subtype.ext
    exact rotation_zero _
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, projectiveZ_add, ih, pow_succ]

theorem projectiveD_pow_eight : projectiveD ^ 8 = 1 := by
  unfold projectiveD
  rw [← projectiveZ_nsmul]
  have hAngle : ((8 : ℕ) : ℝ) * eighthTurn = Real.pi := by
    push_cast
    unfold eighthTurn
    ring
  rw [hAngle]
  unfold projectiveZ
  have hNon : ¬ IsScalar SinglePauli.Z.matrix := by
    rintro ⟨z, hz⟩
    have h₀ := congrArg (fun M : Operator (Fin 2) => M 0 0) hz
    have h₁ := congrArg (fun M : Operator (Fin 2) => M 1 1) hz
    norm_num [SinglePauli.matrix, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] at h₀ h₁
    exact (by norm_num : (1 : ℂ) ≠ -1) (h₀.trans h₁.symm)
  exact (projectiveRotation_eq_one_iff _ _ hNon _).mpr ⟨1, by norm_num⟩

/-- D multiplied seven times realizes T as a projective class. -/
theorem projectiveD_pow_seven_eq_T : projectiveD ^ 7 = projectiveT := by
  rw [← projectiveD_inv_eq_T]
  have h : projectiveD ^ 7 * projectiveD = 1 := by
    rw [← pow_succ]
    exact projectiveD_pow_eight
  calc
    projectiveD ^ 7 = (projectiveD ^ 7 * projectiveD) * projectiveD⁻¹ := by
      rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = _ := by rw [h, one_mul]

#print axioms projectiveD_pow_eight
#print axioms projectiveD_pow_seven_eq_T

end

end CriticalDepth.Manuscript20261114.CliffordT
