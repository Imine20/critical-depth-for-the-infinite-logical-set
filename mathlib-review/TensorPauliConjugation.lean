import TensorPauliTangents

/-!
# Exact quarter-turn conjugation of Pauli rotations
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped BigOperators

noncomputable section

/-- Tensor Pauli labels multiply by forgetting the single-site phase. -/
def unsignedPauliProduct : SinglePauli → SinglePauli → SinglePauli
  | .I, b => b
  | a, .I => a
  | .X, .X | .Y, .Y | .Z, .Z => .I
  | .X, .Y | .Y, .X => .Z
  | .Y, .Z | .Z, .Y => .X
  | .Z, .X | .X, .Z => .Y

abbrev pauliLabelsAnticommute (a b : SinglePauli) : Prop :=
  a ≠ .I ∧ b ≠ .I ∧ a ≠ b

private def pauliProductPhase (a b : SinglePauli) : ℂ :=
  if a = .X ∧ b = .Y ∨ a = .Y ∧ b = .Z ∨ a = .Z ∧ b = .X then Complex.I
  else if pauliLabelsAnticommute a b then -Complex.I
  else 1

private theorem singlePauli_product_with_phase (a b : SinglePauli) :
    a.matrix * b.matrix =
      pauliProductPhase a b • (unsignedPauliProduct a b).matrix := by
  cases a <;> cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliProductPhase, pauliLabelsAnticommute, unsignedPauliProduct,
      SinglePauli.matrix, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Complex.I_mul_I]

private theorem singlePhase_eq_one {a b : SinglePauli} (h : ¬ pauliLabelsAnticommute a b) :
    pauliProductPhase a b = 1 := by
  cases a <;> cases b <;> simp_all [pauliProductPhase, pauliLabelsAnticommute]

private theorem singlePhase_eq_I_or_neg_I {a b : SinglePauli}
    (h : pauliLabelsAnticommute a b) :
    pauliProductPhase a b = Complex.I ∨ pauliProductPhase a b = -Complex.I := by
  cases a <;> cases b <;> simp_all [pauliProductPhase, pauliLabelsAnticommute]

private theorem singleCommSign_eq_neg_one {a b : SinglePauli}
    (h : pauliLabelsAnticommute a b) : a.commutationSign b = -1 := by
  simp [SinglePauli.commutationSign, h.1, h.2.1, h.2.2]

private theorem singleCommSign_eq_one {a b : SinglePauli}
    (h : ¬ pauliLabelsAnticommute a b) : a.commutationSign b = 1 := by
  by_cases hA : a = .I
  · simp [SinglePauli.commutationSign, hA]
  by_cases hB : b = .I
  · simp [SinglePauli.commutationSign, hB]
  have he : a = b := Classical.not_not.mp fun he => h ⟨hA, hB, he⟩
  simp [SinglePauli.commutationSign, he]

variable {k : ℕ}

private theorem tensorPauli_anticommute_at_one (p q : Fin k → SinglePauli) (i : Fin k)
    (ha : pauliLabelsAnticommute (p i) (q i))
    (ho : ∀ j, j ≠ i → ¬ pauliLabelsAnticommute (p j) (q j)) :
    pauliMatrix 0 p * pauliMatrix 0 q = -(pauliMatrix 0 q * pauliMatrix 0 p) := by
  have hs : (∏ j, (p j).commutationSign (q j)) = -1 := by
    rw [Finset.prod_eq_single i]
    · exact singleCommSign_eq_neg_one ha
    · exact fun j _ hj => singleCommSign_eq_one (ho j hj)
    · simp
  simpa only [hs, neg_one_smul] using unphased_pauliMatrix_commutation p q

private theorem tensorPauli_product_at_one (p q : Fin k → SinglePauli) (i : Fin k)
    (ha : pauliLabelsAnticommute (p i) (q i))
    (ho : ∀ j, j ≠ i → ¬ pauliLabelsAnticommute (p j) (q j)) :
    ∃ z : ℂ, (z = 1 ∨ z = -1) ∧
      Complex.I • (pauliMatrix 0 p * pauliMatrix 0 q) =
        z • pauliMatrix 0 (fun j => unsignedPauliProduct (p j) (q j)) := by
  have hs : (∏ j, pauliProductPhase (p j) (q j)) = pauliProductPhase (p i) (q i) := by
    apply Finset.prod_eq_single i
    · exact fun j _ hj => singlePhase_eq_one (ho j hj)
    · simp
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  simp_rw [singlePauli_product_with_phase]
  rw [tensorEntries_smul, hs, smul_smul]
  rcases singlePhase_eq_I_or_neg_I ha with h | h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [h, Complex.I_mul_I]
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [h, mul_neg, Complex.I_mul_I, neg_neg]

private theorem quarterTurn_conjugates_anticommuting {ι : Type*}
    [Fintype ι] [DecidableEq ι] {P Q : Operator ι} (hSelf : star P = P)
    (hSq : P * P = 1) (hAnti : P * Q = -(Q * P)) :
    rotation P (Real.pi / 4) * Q * star (rotation P (Real.pi / 4)) =
      Complex.I • (P * Q) := by
  let c : ℂ := (Real.sqrt 2 / 2 : ℝ)
  have hc : c * c = 1 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hr : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by nlinarith
    change ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1 / 2
    have hz := congrArg (fun x : ℝ => (x : ℂ)) hr
    simpa using hz
  have hcI : (Complex.I * c) * (Complex.I * c) = -(1 / 2 : ℂ) := by
    rw [imag_mul_imag, hc]
  have hMixed : c * (Complex.I * c) = Complex.I * (1 / 2) := by
    calc
      c * (Complex.I * c) = Complex.I * (c * c) := by ring
      _ = _ := by rw [hc]
  have hQP : Q * P = -(P * Q) := by
    rw [hAnti, neg_neg]
  have hPQP : P * Q * P = -Q := by
    rw [hAnti, neg_mul, Matrix.mul_assoc, hSq, Matrix.mul_one]
  rw [star_rotation hSelf]
  simp only [rotation, affine, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four, Complex.ofReal_neg, mul_neg, Matrix.add_mul, Matrix.mul_add,
    smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hQP, hPQP]
  change c • (c • Q + (Complex.I * c) • (P * Q)) +
      -(Complex.I * c) • (c • -(P * Q) + (Complex.I * c) • -Q) = _
  have hm' : (Complex.I * c) * c = Complex.I * (1 / 2) :=
    (mul_comm _ _).trans hMixed
  simp only [smul_add, smul_smul, neg_mul, hc, hm', hMixed, hcI, neg_neg, neg_smul, smul_neg]
  calc
    _ = (Complex.I * (1 / 2 : ℂ)) • (P * Q) +
          (Complex.I * (1 / 2 : ℂ)) • (P * Q) := by abel
    _ = _ := by rw [← add_smul, show Complex.I * (1 / 2 : ℂ) +
      Complex.I * (1 / 2 : ℂ) = Complex.I by ring]

private theorem rotation_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (P : Operator ι) (t : ℝ) :
    U.val * rotation P t * (U⁻¹).val =
      rotation (U.val * P * (U⁻¹).val) t := by
  have h : U.val * (U⁻¹).val = 1 := U.property.2
  simp only [rotation, affine, Matrix.mul_add, Matrix.add_mul, smul_mul_assoc,
    mul_smul_comm, Matrix.mul_one, h]

private theorem rotation_neg_direction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Operator ι) (t : ℝ) : rotation (-P) t = rotation P (-t) := by
  simp [rotation, affine, Real.cos_neg, Real.sin_neg, smul_neg]

variable (G : Subgroup (PU (QubitBasis k)))

/-- The Pauli directions whose full one-parameter rotations belong to G. -/
def HasTensorPauliRotations (p : Fin k → SinglePauli) : Prop :=
  ∀ t, projectiveMk (QubitBasis k) (tensorPauliRotation p t) ∈ G

/-- A quarter-turn about one included Pauli sends a second included Pauli
to the unsigned product, provided exactly one site anticommutes. -/
theorem hasTensorPauliRotations_unsignedProduct
    (p q : Fin k → SinglePauli) (i : Fin k)
    (hp : HasTensorPauliRotations G p) (hq : HasTensorPauliRotations G q)
    (ha : pauliLabelsAnticommute (p i) (q i))
    (ho : ∀ j, j ≠ i → ¬ pauliLabelsAnticommute (p j) (q j)) :
    HasTensorPauliRotations G (fun j => unsignedPauliProduct (p j) (q j)) := by
  let U := tensorPauliRotation p (Real.pi / 4)
  let r : Fin k → SinglePauli := fun j => unsignedPauliProduct (p j) (q j)
  have hU : projectiveMk (QubitBasis k) U ∈ G := hp _
  obtain ⟨z, hz, hProd⟩ := tensorPauli_product_at_one p q i ha ho
  have hc : U.val * pauliMatrix 0 q * (U⁻¹).val = z • pauliMatrix 0 r :=
    (quarterTurn_conjugates_anticommuting (unphased_pauliMatrix_selfAdjoint p)
      (unphased_pauliMatrix_sq p) (tensorPauli_anticommute_at_one p q i ha ho)).trans hProd
  intro t
  rcases hz with rfl | rfl
  · have hEq : U * tensorPauliRotation q t * U⁻¹ = tensorPauliRotation r t := by
      apply Subtype.ext
      change U.val * rotation (pauliMatrix 0 q) t * (U⁻¹).val = rotation (pauliMatrix 0 r) t
      rw [rotation_conjugate, hc, one_smul]
    rw [← hEq, map_mul, map_mul, map_inv]
    exact G.mul_mem (G.mul_mem hU (hq t)) (G.inv_mem hU)
  · have hEq : U * tensorPauliRotation q (-t) * U⁻¹ = tensorPauliRotation r t := by
      apply Subtype.ext
      change U.val * rotation (pauliMatrix 0 q) (-t) * (U⁻¹).val = rotation (pauliMatrix 0 r) t
      rw [rotation_conjugate, hc, neg_one_smul, rotation_neg_direction, neg_neg]
    rw [← hEq, map_mul, map_mul, map_inv]
    exact G.mul_mem (G.mul_mem hU (hq (-t))) (G.inv_mem hU)

#print axioms hasTensorPauliRotations_unsignedProduct

end

end CriticalDepth.Manuscript20261114
