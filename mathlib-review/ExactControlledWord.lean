import ExactControlledTarget

/-!
# Finite Pauli words for a fully controlled one-qubit unitary
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open CriticalDepth.Manuscript20261114.OneQubitEuler

noncomputable section

variable {k : ℕ}

private theorem exists_euler_with_phase (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (a s t u : ℝ),
      U.val = ((Circle.exp a : ℂ) • (1 : Operator (Fin 2))) *
        rotation SinglePauli.Z.matrix s * rotation SinglePauli.X.matrix t *
        rotation SinglePauli.Z.matrix u := by
  obtain ⟨s, t, u, h⟩ := projective_euler_zxz (projectiveMk (Fin 2) U)
  let Z1 := unitaryRotation SinglePauli.Z.matrix (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) s
  let X := unitaryRotation SinglePauli.X.matrix (singlePauli_selfAdjoint .X) (singlePauli_sq .X) t
  let Z2 := unitaryRotation SinglePauli.Z.matrix (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) u
  change projectiveMk (Fin 2) U = projectiveMk (Fin 2) Z1 * projectiveMk (Fin 2) X *
    projectiveMk (Fin 2) Z2 at h
  rw [← map_mul, ← map_mul] at h
  obtain ⟨z, hz, hM⟩ := (projectiveMk_eq_iff (Fin 2) _ _).mp h
  have hnorm : ‖z‖ = 1 := by
    have hz' := hz
    rw [mul_comm, show star z = starRingEnd ℂ z from rfl, Complex.mul_conj'] at hz'
    apply (sq_eq_sq₀ (norm_nonneg z) (by positivity : (0 : ℝ) ≤ 1)).mp
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re, one_pow]
      using congrArg Complex.re hz'
  let c : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hnorm⟩
  obtain ⟨a, ha⟩ := Circle.exp_surjective c
  refine ⟨a, s, t, u, ?_⟩
  have ha' : (Circle.exp a : ℂ) = z := congrArg (fun x : Circle => (x : ℂ)) ha
  rw [ha']
  change U.val = (z • (1 : Operator (Fin 2))) * Z1.val * X.val * Z2.val
  rw [smul_mul_assoc, Matrix.one_mul, smul_mul_assoc, smul_mul_assoc]
  exact hM

/-- The registered class of a tensor Pauli with its real angle. -/
abbrev TensorPauliWord (k : ℕ) := List (Matrix.unitaryGroup (QubitBasis k) ℂ)

def IsTensorPauliWord (L : TensorPauliWord k) : Prop :=
  ∀ A ∈ L, ∃ w : Fin k → SinglePauli, ∃ t : ℝ, A = tensorPauliRotation w t

private theorem isTensorPauliWord_append {L R : TensorPauliWord k}
    (hL : IsTensorPauliWord L) (hR : IsTensorPauliWord R) :
    IsTensorPauliWord (L ++ R) := by
  intro A h
  rcases List.mem_append.mp h with h | h
  · exact hL A h
  · exact hR A h

/-- Retaining the local global phase as a *conditional phase* produces
the complete two-level unitary as a word of exact rotations. -/
theorem controlledTarget_exists_tensorPauliWord
    (j : Fin k) (p : QubitBasis k) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ L : TensorPauliWord k, IsTensorPauliWord L ∧ L.prod.val = controlledTarget j p U.val := by
  let B := controlComplements j
  have hj : j ∉ B := Finset.notMem_erase _ _
  obtain ⟨a, s, t, u, hEuler⟩ := exists_euler_with_phase U
  obtain ⟨L₀, h₀, hP⟩ := conditionalPhase_eq_finite_tensorPauliWord B p a
  obtain ⟨L₁, h₁, hA⟩ := conditionalRotation_eq_finite_tensorPauliWord B p j hj .Z s
  obtain ⟨L₂, h₂, hB⟩ := conditionalRotation_eq_finite_tensorPauliWord B p j hj .X t
  obtain ⟨L₃, h₃, hC⟩ := conditionalRotation_eq_finite_tensorPauliWord B p j hj .Z u
  have hword₀ : IsTensorPauliWord L₀ := by
    intro A hA
    obtain ⟨T, _, hT⟩ := h₀ A hA
    exact ⟨zSubset T, conditionalPauliAngle B T p a, hT⟩
  have hword (L : TensorPauliWord k) (d : SinglePauli) (r : ℝ)
      (h : ∀ A ∈ L, ∃ T : Finset (Fin k), T ⊆ B ∧
        A = tensorPauliRotation (controlledPauliWord T j d) (conditionalPauliAngle B T p r)) :
      IsTensorPauliWord L := by
    intro A hA
    obtain ⟨T, _, hT⟩ := h A hA
    exact ⟨controlledPauliWord T j d, conditionalPauliAngle B T p r, hT⟩
  refine ⟨((L₀ ++ L₁) ++ L₂) ++ L₃,
    isTensorPauliWord_append
      (isTensorPauliWord_append
        (isTensorPauliWord_append hword₀ (hword L₁ .Z s h₁)) (hword L₂ .X t h₂))
      (hword L₃ .Z u h₃), ?_⟩
  rw [List.prod_append, List.prod_append, List.prod_append]
  change L₀.prod.val * L₁.prod.val * L₂.prod.val * L₃.prod.val = _
  rw [hP, hA, hB, hC, ← controlledTarget_rotation, ← controlledTarget_rotation,
    ← controlledTarget_rotation, ← controlledTarget_scalar, controlledTarget_mul,
    controlledTarget_mul, controlledTarget_mul, ← hEuler]

#print axioms controlledTarget_exists_tensorPauliWord

end

end CriticalDepth.Manuscript20261114
