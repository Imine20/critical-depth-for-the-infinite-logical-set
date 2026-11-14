import CliffordTDenseCircle
import CliffordTTangents

/-!
# Density of the logical Hadamard and T classes
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114.OneQubitEuler Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

private def phaseLift (t : ℝ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  unitaryRotation (1 : QubitOperator) (by simp) (by simp) t

private theorem phaseLift_projection (t : ℝ) : projectiveMk (Fin 2) (phaseLift t) = 1 := by
  rw [← map_one (projectiveMk (Fin 2))]
  apply (projectiveMk_eq_iff (Fin 2) _ _).mpr
  refine ⟨(Circle.exp t : ℂ), circle_star_mul_self _, ?_⟩
  change rotation (1 : QubitOperator) t = _
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
  simp [rotation, affine, add_smul, mul_comm]

private def quarterTurn : Matrix.unitaryGroup (Fin 2) ℂ :=
  unitaryRotation SinglePauli.Z.matrix (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z)
    (Real.pi / 4)

private theorem quarterTurn_projection : projectiveMk (Fin 2) quarterTurn = projectiveD ^ 2 := by
  change projectiveZ (Real.pi / 4) = projectiveZ eighthTurn ^ 2
  rw [pow_two, ← projectiveZ_add]
  congr 1
  unfold eighthTurn
  ring

private theorem quarterTurn_conj (a b c : ℝ) :
    quarterTurn.val * pauliCombination a b c * (quarterTurn⁻¹).val =
      pauliCombination b (-a) c := by
  change rotation SinglePauli.Z.matrix (Real.pi / 4) * pauliCombination a b c *
    star (rotation SinglePauli.Z.matrix (Real.pi / 4)) = _
  have h : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  let s : ℂ := (Real.sqrt 2 / 2 : ℝ)
  have hc : s ^ 2 = 1 / 2 := by
    have H := congrArg (fun x : ℝ => (x : ℂ)) h
    simpa [s] using H
  have hCos : (Real.cos (Real.pi / 4) : ℂ) = s := by rw [Real.cos_pi_div_four]
  have hSin : (Real.sin (Real.pi / 4) : ℂ) = s := by rw [Real.sin_pi_div_four]
  rw [star_rotation (singlePauli_selfAdjoint .Z)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotation, affine, pauliCombination, SinglePauli.matrix, Real.cos_neg,
      Real.sin_neg, Complex.ofReal_neg, hCos, hSin, Matrix.mul_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two] <;>
    simp [Matrix.one_apply, Fin.ext_iff] <;> ring_nf <;> try simp only [Complex.I_sq,
      show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq, neg_one_mul]]
  · linear_combination 2 * (c : ℂ) * hc
  · linear_combination (2 * (b : ℂ) + 2 * Complex.I * (a : ℂ)) * hc
  · linear_combination (2 * (b : ℂ) - 2 * Complex.I * (a : ℂ)) * hc
  · linear_combination 2 * (c : ℂ) * hc

private theorem quarterTurn_conj_twice (a b c : ℝ) :
    (quarterTurn * quarterTurn).val * pauliCombination a b c *
      ((quarterTurn * quarterTurn)⁻¹).val = pauliCombination (-a) (-b) c := by
  simp only [_root_.mul_inv_rev]
  change quarterTurn.val * quarterTurn.val * pauliCombination a b c *
    ((quarterTurn⁻¹).val * (quarterTurn⁻¹).val) = _
  calc
    _ = quarterTurn.val *
      (quarterTurn.val * pauliCombination a b c * (quarterTurn⁻¹).val) *
        (quarterTurn⁻¹).val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [quarterTurn_conj, quarterTurn_conj]

private def liftMixed (t : ℝ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  unitaryRotation mixedAxis mixedAxis_selfAdjoint mixedAxis_sq t

private def curves : Option (Fin 3) → ℝ → Matrix.unitaryGroup (Fin 2) ℂ
  | none => phaseLift
  | some i => fun t => quarterTurn ^ i.val * liftMixed t * (quarterTurn ^ i.val)⁻¹

private def mixedTangents : Option (Fin 3) → QubitOperator
  | none => pauliTangent 0 0 0 1
  | some i => (quarterTurn ^ i.val).val * (Complex.I • mixedAxis) *
      ((quarterTurn ^ i.val)⁻¹).val

private theorem mixedTangents_span :
    skewAdjoint.submodule ℝ QubitOperator ≤ Submodule.span ℝ (Set.range mixedTangents) := by
  have hXY : mixedAxisX ^ 2 + mixedAxisY ^ 2 ≠ 0 := by
    have h := sq_pos_of_pos mixedAxisX_pos
    nlinarith [sq_nonneg mixedAxisY]
  have hZ : mixedAxisZ ≠ 0 := ne_of_gt mixedAxisZ_pos
  refine (skewAdjoint_le_span_of_pauliTangent_quarter_turns hXY hZ).trans (Submodule.span_mono ?_)
  intro A hA
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl | rfl | rfl
  · exact ⟨none, rfl⟩
  · refine ⟨some 0, ?_⟩
    simp [mixedTangents, pauliTangent, mixedAxis]
  · refine ⟨some 1, ?_⟩
    simp only [mixedTangents, show (1 : Fin 3).val = 1 from rfl, pow_one]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    unfold mixedAxis
    rw [quarterTurn_conj]
    simp [pauliTangent]
  · refine ⟨some 2, ?_⟩
    simp only [mixedTangents, show (2 : Fin 3).val = 2 from rfl]
    rw [pow_two, Matrix.mul_smul, Matrix.smul_mul]
    unfold mixedAxis
    rw [quarterTurn_conj_twice]
    simp [pauliTangent]

/-- The Hadamard and T classes generate a dense subgroup of the qubit
projective unitary group. -/
theorem dense_of_contains_H_T (G : Subgroup (PU (Fin 2)))
    (hH : projectiveHadamard ∈ G) (hT : projectiveT ∈ G) :
    G.topologicalClosure = ⊤ := by
  have hD : projectiveD ∈ G := by
    have h := G.inv_mem hT
    rw [← projectiveD_inv_eq_T, inv_inv] at h
    exact h
  have hX : projectiveX eighthTurn ∈ G := by
    rw [← projectiveHadamard_conjugates_rotationZ]
    exact G.mul_mem (G.mul_mem hH hD) (G.inv_mem hH)
  have hProduct : projectiveRotation mixedAxis mixedAxis_selfAdjoint mixedAxis_sq
      mixedQubitAngle ∈ G := by
    rw [← projectiveZ_mul_projectiveX_eighthTurn]
    exact G.mul_mem hD hX
  let C := G.topologicalClosure
  have hCircle : circleRotationSubgroup mixedAxis mixedAxis_selfAdjoint mixedAxis_sq ≤ C :=
    circleRotationSubgroup_le_topologicalClosure_of_irrational G mixedAxis mixedAxis_selfAdjoint
      mixedAxis_sq mixedQubitAngle mixedQubitAngle_irrational hProduct
  have hQ : projectiveMk (Fin 2) quarterTurn ∈ C := by
    rw [quarterTurn_projection]
    exact G.le_topologicalClosure (G.pow_mem hD 2)
  apply eq_top_of_closed_spanning_unitary_curves C (Subgroup.isClosed_topologicalClosure G)
    curves ?_ ?_ ?_ mixedTangents ?_ mixedTangents_span
  · intro i
    cases i <;> simp [curves, phaseLift, liftMixed, unitaryRotation]
  · intro i t
    cases i with
    | none =>
      rw [show curves none t = phaseLift t from rfl, phaseLift_projection]
      exact C.one_mem
    | some i =>
      change projectiveMk (Fin 2) (quarterTurn ^ i.val * liftMixed t * (quarterTurn ^ i.val)⁻¹) ∈ C
      simp only [map_mul, map_inv, map_pow]
      have h : projectiveMk (Fin 2) (liftMixed t) ∈ C := by
        apply hCircle
        exact (mem_circleRotationSubgroup_iff _ _ _ _).mpr ⟨t, rfl⟩
      exact C.mul_mem (C.mul_mem (C.pow_mem hQ i.val) h) (C.inv_mem (C.pow_mem hQ i.val))
  · intro i
    cases i with
    | none => exact rotation_contDiffAt_zero 1
    | some i =>
      change ContDiffAt ℝ 1 (fun t => (quarterTurn ^ i.val).val * rotation mixedAxis t *
        ((quarterTurn ^ i.val)⁻¹).val) 0
      exact (contDiffAt_const.mul (rotation_contDiffAt_zero mixedAxis)).mul contDiffAt_const
  · intro i
    cases i with
    | none => simpa [curves, phaseLift, unitaryRotation, mixedTangents, pauliTangent, pauliCombination]
        using rotation_hasDerivAt_zero 1
    | some i => exact ((rotation_hasDerivAt_zero mixedAxis).const_mul
        (quarterTurn ^ i.val).val).mul_const ((quarterTurn ^ i.val)⁻¹).val

/-- Membership of the two Q37 depth-one classes already suffices for
density of finite words. -/
theorem dense_of_contains_D_B (G : Subgroup (PU (Fin 2)))
    (hD : projectiveD ∈ G) (hB : projectiveB ∈ G) :
    G.topologicalClosure = ⊤ := by
  apply dense_of_contains_H_T G
  · rw [← projectiveD_sq_mul_B_mul_D_sq]
    exact G.mul_mem (G.mul_mem (G.pow_mem hD 2) hB) (G.pow_mem hD 2)
  · rw [← projectiveD_inv_eq_T]
    exact G.inv_mem hD

#print axioms dense_of_contains_H_T
#print axioms dense_of_contains_D_B

end

end CriticalDepth.Manuscript20261114.CliffordT
