import CriticalDepth.Rotations

namespace CriticalDepth.Examples

def pauliZ : Operator (Fin 2) := !![1, 0; 0, -1]

theorem pauliZ_selfAdjoint : star pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_not_isScalar : ¬ IsScalar pauliZ := by
  rintro ⟨z, hz⟩
  have h0 := congrArg (fun A : Operator (Fin 2) => A 0 0) hz
  have h1 := congrArg (fun A : Operator (Fin 2) => A 1 1) hz
  simp [pauliZ] at h0 h1
  have : (1 : ℂ) = -1 := h0.trans h1.symm
  norm_num at this

/-- A real call supplying all hypotheses to the general family theorem. -/
example : Continuous (rotation pauliZ) ∧
    rotation pauliZ 0 = 1 ∧
    (∀ s t : ℝ, rotation pauliZ (s + t) = rotation pauliZ s * rotation pauliZ t) ∧
    (∀ t : ℝ, IsUnitary (rotation pauliZ t)) ∧
    ¬ ProjectivelyEquivalent (rotation pauliZ (Real.pi / 2)) 1 := by
  exact rotation_one_parameter_family pauliZ_selfAdjoint pauliZ_sq pauliZ_not_isScalar

example : IsUnitary (rotation pauliZ (3 / 7)) := by
  exact rotation_isUnitary pauliZ_selfAdjoint pauliZ_sq (3 / 7)

example (r : ℕ) : IsUnitary (rationalRotation pauliZ r) := by
  exact rationalRotation_isUnitary pauliZ_selfAdjoint pauliZ_sq r

example : Set.Infinite
    (Set.range (fun r : ℕ => projectiveClass (rationalRotation pauliZ r))) := by
  exact rationalRotation_classes_infinite pauliZ_not_isScalar

#print axioms CriticalDepth.affine_coefficients_unique
#print axioms CriticalDepth.rotation_one_parameter_family
#print axioms CriticalDepth.rationalRotation_isUnitary
#print axioms CriticalDepth.rationalRotation_classes_infinite
#print axioms CriticalDepth.Examples.pauliZ_not_isScalar

end CriticalDepth.Examples
