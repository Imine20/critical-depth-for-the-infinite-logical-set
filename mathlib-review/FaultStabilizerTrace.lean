import CriticalDepthMathlib
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The minimum-weight stabilizer logical Pauli is traceless

The sum of all stabilizers has image in the whole fixed subspace. Its
compression is the group cardinality times identity. Pauli trace
orthogonality then rules out a nonzero trace for a nonscalar
code-preserving Pauli action.
-/

open scoped BigOperators Kronecker

namespace CriticalDepth.FaultStabilizerTrace

open CriticalDepth.Manuscript
open Matrix

/-- Tensor Pauli matrices with distinct unphased words are trace-orthogonal. -/
theorem pauli_mul_trace_eq_zero_of_ne {n : ℕ} {p q : Fin n → SinglePauli}
    (hpq : p ≠ q) :
    (pauliMatrix 0 p * pauliMatrix 0 q).trace = 0 := by
  classical
  have hlocal (a b : SinglePauli) (hab : a ≠ b) : (a.matrix * b.matrix).trace = 0 := by
    cases a <;> cases b <;>
      simp_all [SinglePauli.matrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Fin.sum_univ_two, Complex.I_mul_I]
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ q i := by
    by_contra! h
    exact hpq (funext h)
  rw [pauliMatrix_zero_eq_tensorEntries, pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  let entry (j : Fin n) (x : Fin 2) := ((p j).matrix * (q j).matrix) x x
  change (∑ x : (Fin n → Fin 2), ∏ j : Fin n, entry j (x j)) = 0
  rw [← Fintype.prod_sum entry]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact hlocal (p i) (q i) hi

section FixedSpace

variable {Phys Enc : Type*} [Fintype Phys] [DecidableEq Phys] [Fintype Enc] [DecidableEq Enc]

/-- The unnormalized sum of the stabilizer matrices maps every vector
to the common fixed space. -/
private theorem subgroup_sum_fixed
    (S : Subgroup (Matrix.unitaryGroup Phys ℂ)) [Fintype S] (U : S) :
    (U.val : Matrix Phys Phys ℂ) * (∑ T : S, (T.val : Matrix Phys Phys ℂ)) =
      ∑ T : S, (T.val : Matrix Phys Phys ℂ) := by
  let perm : S ≃ S :=
    { toFun := fun T => U * T
      invFun := fun T => U⁻¹ * T
      left_inv := by intro T; simp
      right_inv := by intro T; simp }
  rw [Matrix.mul_sum]
  exact perm.sum_comp (fun T : S => (T.val : Matrix Phys Phys ℂ))

/-- The finite subgroup sum is its cardinality times the encoding range
projector. The whole-fixed-space hypothesis is used for the range inclusion. -/
theorem subgroup_sum_eq_card_smul_projector (V : Matrix Phys Enc ℂ)
    (hV : V.conjTranspose * V = 1)
    (S : Subgroup (Matrix.unitaryGroup Phys ℂ)) [Fintype S]
    (hspace : Set.range (fun v => V.mulVec v) =
      {v | ∀ U ∈ S, (U : Matrix Phys Phys ℂ).mulVec v = v}) :
    (∑ T : S, (T.val : Matrix Phys Phys ℂ)) =
      (Fintype.card S : ℂ) • (V * V.conjTranspose) := by
  classical
  let Q : Matrix Phys Phys ℂ := ∑ T : S, (T.val : Matrix Phys Phys ℂ)
  have hfix (T : S) : (T.val : Matrix Phys Phys ℂ) * V = V := by
    ext x j
    let e : Enc → ℂ := fun k => if k = j then 1 else 0
    have hv : V.mulVec e ∈ Set.range (fun w => V.mulVec w) := ⟨e, rfl⟩
    rw [hspace] at hv
    have hh := congrFun (hv T.val T.property) x
    change (((T.val : Matrix Phys Phys ℂ) *ᵥ (V *ᵥ e)) x) = (V *ᵥ e) x at hh
    rw [Matrix.mulVec_mulVec] at hh
    simpa [Matrix.mulVec, dotProduct, e, mul_ite] using hh
  have hQV : Q * V = (Fintype.card S : ℂ) • V := by
    dsimp only [Q]
    rw [Matrix.sum_mul]
    simp only [hfix, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hVQ : (V * V.conjTranspose) * Q = Q := by
    ext x j
    let e : Phys → ℂ := fun k => if k = j then 1 else 0
    have hv : Q.mulVec e ∈ Set.range (fun w => V.mulVec w) := by
      rw [hspace]
      intro U hU
      have hu := congrArg (fun M : Matrix Phys Phys ℂ => M.mulVec e)
        (subgroup_sum_fixed S ⟨U, hU⟩)
      rw [Matrix.mulVec_mulVec]
      exact hu
    obtain ⟨w, hw⟩ := hv
    have hproj : (V * V.conjTranspose) * V = V := by
      rw [Matrix.mul_assoc, hV, Matrix.mul_one]
    have hh : ((V * V.conjTranspose) * Q).mulVec e = Q.mulVec e := by
      rw [← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, hproj]
    simpa [Matrix.mulVec, dotProduct, e, mul_ite] using congrFun hh x
  have hQstar : Q.conjTranspose = Q := by
    let perm : S ≃ S :=
      { toFun := Inv.inv
        invFun := Inv.inv
        left_inv := inv_inv
        right_inv := inv_inv }
    dsimp only [Q]
    rw [Matrix.conjTranspose_sum]
    change (∑ T : S, star (T.val : Matrix Phys Phys ℂ)) = _
    have hinv (T : S) : (((T⁻¹ : S).val : Matrix.unitaryGroup Phys ℂ) : Matrix Phys Phys ℂ) =
        star (T.val : Matrix Phys Phys ℂ) := rfl
    have hperm : (∑ T : S, ((T⁻¹ : S).val : Matrix Phys Phys ℂ)) =
        ∑ T : S, (T.val : Matrix Phys Phys ℂ) :=
      perm.sum_comp (fun T : S => (T.val : Matrix Phys Phys ℂ))
    simpa only [hinv] using hperm
  have hQP : Q * (V * V.conjTranspose) = Q := by
    have h := congrArg Matrix.conjTranspose hVQ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQstar] at h
  change Q = _
  rw [← hQP, ← Matrix.mul_assoc, hQV, Matrix.smul_mul]

end FixedSpace

/-- A nonscalar code-preserving physical Pauli has traceless logical action. -/
theorem stabilizer_logicalPauli_trace_zero {n k : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstabilizer : IsStabilizer C)
    (p : Fin n → SinglePauli) (W : Operator (Fin (2 ^ k)))
    (hencoded : pauliMatrix (0 : Fin 4) p * C.encoding =
      C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))))
    (hnonscalar : ¬ IsScalar W) :
    W.trace = 0 := by
  classical
  obtain ⟨S, hS, hspace⟩ := hstabilizer
  have hfinite : (S : Set (Matrix.unitaryGroup (QubitBasis n) ℂ)).Finite := by
    have h := (ReviewV2.pauliOperator_set_finite n).preimage
      (f := fun U : Matrix.unitaryGroup (QubitBasis n) ℂ => U.val) Subtype.val_injective.injOn
    exact h.subset (fun U hU => hS U hU)
  letI : Fintype S := hfinite.fintype
  let P := pauliMatrix (0 : Fin 4) p
  have htraceTerm (T : S) : (P * (T.val : Operator (QubitBasis n))).trace = 0 := by
    obtain ⟨phase, q, hq⟩ := hS T.val T.property
    by_cases hpq : p = q
    · subst q
      have hfix := encoding_fixed_of_fixedSpace C S hspace T.val T.property
      rw [hq, pauliMatrix_eq_phase_smul, Matrix.smul_mul, hencoded] at hfix
      have hz : Complex.I ^ phase.val ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
      have hfix' : C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))) =
          (Complex.I ^ phase.val)⁻¹ • C.encoding := by
        have hh := congrArg (fun A => (Complex.I ^ phase.val)⁻¹ • A) hfix
        simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using hh
      have hcompress : (W ⊗ₖ (1 : Operator (Fin 1))) =
          (Complex.I ^ phase.val)⁻¹ • (1 : Operator (Fin (2 ^ k) × Fin 1)) := by
        have hh := congrArg (fun A => C.encoding.conjTranspose * A) hfix'
        change C.encoding.conjTranspose * (C.encoding * (W ⊗ₖ (1 : Operator (Fin 1)))) =
          C.encoding.conjTranspose * ((Complex.I ^ phase.val)⁻¹ • C.encoding) at hh
        rw [← Matrix.mul_assoc, C.isometry, Matrix.one_mul, Matrix.mul_smul, C.isometry] at hh
        exact hh
      apply False.elim
      apply hnonscalar
      refine ⟨(Complex.I ^ phase.val)⁻¹, ?_⟩
      ext i j
      have hh := congrArg (fun A : Operator (Fin (2 ^ k) × Fin 1) => A (i, 0) (j, 0)) hcompress
      simpa [Matrix.kronecker_apply, Matrix.one_apply] using hh
    · rw [hq, pauliMatrix_eq_phase_smul, Matrix.mul_smul, Matrix.trace_smul]
      rw [show (P * pauliMatrix 0 q).trace = 0 from pauli_mul_trace_eq_zero_of_ne hpq, smul_zero]
  have htotal : (P * (∑ T : S, (T.val : Operator (QubitBasis n)))).trace = 0 := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    simp [htraceTerm]
  have hcompress : C.encoding.conjTranspose * (P * C.encoding) =
      W ⊗ₖ (1 : Operator (Fin 1)) := by
    change C.encoding.conjTranspose * (pauliMatrix 0 p * C.encoding) = _
    rw [hencoded, ← Matrix.mul_assoc, C.isometry, Matrix.one_mul]
  rw [subgroup_sum_eq_card_smul_projector C.encoding C.isometry S hspace,
    Matrix.mul_smul, Matrix.trace_smul, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm (P * C.encoding) C.encoding.conjTranspose,
    hcompress, Matrix.trace_kronecker, Matrix.trace_one, Fintype.card_fin,
    Nat.cast_one, mul_one, smul_eq_mul] at htotal
  have hcard : (Fintype.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp htotal).resolve_left hcard

/-- Actual-distance stabilizer witness with the trace hypothesis used by
the recovery ambiguity estimate. -/
theorem stabilizer_exact_traceless_logicalPauli {n k d : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    ∃ (p : Fin n → SinglePauli) (W : Operator (Fin (2 ^ k))),
      (pauliSupport p).card = d ∧
      pauliMatrix (0 : Fin 4) p * C.encoding =
        C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))) ∧
      star W = W ∧ W * W = 1 ∧ W.trace = 0 := by
  obtain ⟨p, W, hweight, hencoded, hself, hsq, hns⟩ :=
    stabilizer_exact_logicalPauli C hstabilizer hdistance
  exact ⟨p, W, hweight, hencoded, hself, hsq,
    stabilizer_logicalPauli_trace_zero C hstabilizer p W hencoded hns⟩

#print axioms pauli_mul_trace_eq_zero_of_ne
#print axioms subgroup_sum_eq_card_smul_projector
#print axioms stabilizer_logicalPauli_trace_zero
#print axioms stabilizer_exact_traceless_logicalPauli

end CriticalDepth.FaultStabilizerTrace
