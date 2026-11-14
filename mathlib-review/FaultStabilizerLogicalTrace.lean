import FaultStabilizerSyndrome

/-!
# The stabilizer trace pairing on logical Pauli classes

Compression of a physical Pauli can be nonzero only when its syndrome is
trivial. Among centralizing errors, the compressed unitary is traceless
unless the Pauli belongs to a scalar translate of the stabilizer.
-/

namespace CriticalDepth.FaultStabilizerLogicalTrace

noncomputable section

open Matrix
open CriticalDepth.Manuscript CriticalDepth.PauliGroup CriticalDepth.FaultStabilizerTrace
open CriticalDepth.FaultStabilizerSyndrome
open scoped BigOperators

variable {n K : ℕ}
variable (C : Code n (fun _ => 2) K 1)

def compress (P : Operator (QubitBasis n)) : Operator (Fin K × Fin 1) :=
  C.encoding.conjTranspose * P * C.encoding

def compressLinear : Operator (QubitBasis n) →ₗ[ℂ] Operator (Fin K × Fin 1) where
  toFun := compress C
  map_add' := by intro P Q; simp only [compress, Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro z P
    simp only [compress, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem compressLinear_surjective : Function.Surjective (compressLinear C) := by
  intro A
  use C.encoding * A * C.encoding.conjTranspose
  change C.encoding.conjTranspose * (C.encoding * A * C.encoding.conjTranspose) * C.encoding = A
  calc
    _ = (C.encoding.conjTranspose * C.encoding) * A * (C.encoding.conjTranspose * C.encoding) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [C.isometry, Matrix.one_mul, Matrix.mul_one]

variable (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
variable (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})

include hS hspace in
/-- Scalar-or-orthogonal trace criterion for a relative physical Pauli. -/
theorem compress_trace_zero_unless_scalar (P : Operator (QubitBasis n)) (hP : IsPauli P)
    (hnonscalar : ¬ IsScalar (compress C P)) : (compress C P).trace = 0 := by
  classical
  have hfinite : (S : Set (Matrix.unitaryGroup (QubitBasis n) ℂ)).Finite := by
    have h := (ReviewV2.pauliOperator_set_finite n).preimage
      (f := fun U : Matrix.unitaryGroup (QubitBasis n) ℂ => U.val) Subtype.val_injective.injOn
    exact h.subset (fun U hU => hS U hU)
  letI : Fintype S := hfinite.fintype
  obtain ⟨a, p, rfl⟩ := hP
  have htraceTerm (T : S) :
      (pauliMatrix a p * (T.val : Operator (QubitBasis n))).trace = 0 := by
    obtain ⟨b, q, hq⟩ := hS T.val T.property
    by_cases hpq : p = q
    · subst q
      exfalso
      apply hnonscalar
      let z := Complex.I ^ b.val
      have hz : z ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
      have hfix := encoding_fixed_of_fixedSpace C S hspace T.val T.property
      rw [hq, pauliMatrix_eq_phase_smul, Matrix.smul_mul] at hfix
      change z • (pauliMatrix 0 p * C.encoding) = C.encoding at hfix
      have hword : pauliMatrix 0 p * C.encoding = z⁻¹ • C.encoding := by
        have h := congrArg (fun A => z⁻¹ • A) hfix
        simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using h
      refine ⟨Complex.I ^ a.val * z⁻¹, ?_⟩
      unfold compress
      calc
        _ = C.encoding.conjTranspose * (pauliMatrix a p * C.encoding) := Matrix.mul_assoc _ _ _
        _ = C.encoding.conjTranspose * (Complex.I ^ a.val • (z⁻¹ • C.encoding)) := by
          rw [pauliMatrix_eq_phase_smul, Matrix.smul_mul, hword]
        _ = _ := by rw [smul_smul, Matrix.mul_smul, C.isometry]
    · rw [hq, pauliMatrix_eq_phase_smul a p, pauliMatrix_eq_phase_smul b q,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
        pauli_mul_trace_eq_zero_of_ne hpq, smul_zero]
  have htotal : (pauliMatrix a p * (∑ T : S, (T.val : Operator (QubitBasis n)))).trace = 0 := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    simp [htraceTerm]
  rw [subgroup_sum_eq_card_smul_projector C.encoding C.isometry S hspace,
    Matrix.mul_smul, Matrix.trace_smul, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm (pauliMatrix a p * C.encoding) C.encoding.conjTranspose,
    ← Matrix.mul_assoc, smul_eq_mul] at htotal
  have hcard : (Fintype.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp htotal).resolve_left hcard

include hS hspace in
/-- A Pauli that anticommutes with a stabilizer projects to zero. -/
theorem compress_zero_of_not_centralizing (P : Operator (QubitBasis n))
    (hP : IsPauli P)
    (hn : ¬ ∀ T ∈ S, (T : Operator (QubitBasis n)) * P = P * (T : Operator (QubitBasis n))) :
    compress C P = 0 := by
  push Not at hn
  obtain ⟨T, hT, hne⟩ := hn
  have hanti : (T : Operator (QubitBasis n)) * P = -(P * (T : Operator (QubitBasis n))) := by
    obtain ⟨a, x, hx⟩ := hS T hT
    obtain ⟨b, y, hy⟩ := hP
    rw [hx, hy] at hne ⊢
    exact (pauliMatrix_commute_or_anticommute a b x y).resolve_left hne
  have hfix := encoding_fixed_of_fixedSpace C S hspace T hT
  have hU : IsUnitary (T : Operator (QubitBasis n)) := T.property
  have hf := encoding_adjoint_fixed_of_fixed C _ hU hfix
  have h : compress C P = -(compress C P) := by
    unfold compress
    calc
      _ = C.encoding.conjTranspose * ((T : Operator (QubitBasis n)) * P) * C.encoding := by
        rw [← Matrix.mul_assoc, hf]
      _ = _ := by
        rw [hanti, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc (C.encoding.conjTranspose),
          Matrix.mul_assoc P _ _, hfix, ← Matrix.mul_assoc]
  ext i j
  have hh := congrArg (fun M : Operator (Fin K × Fin 1) => M i j) h
  simp only [Matrix.neg_apply, Matrix.zero_apply] at hh ⊢
  linear_combination (1 / 2 : ℂ) * hh

include hS hspace in
/-- All logical matrices are spanned by the compressed centralizing physical
Paulis, without a choice of an a priori logical frame. -/
theorem compressed_centralizingPaulis_span :
    Submodule.span ℂ {A : Operator (Fin K × Fin 1) | ∃ P : Operator (QubitBasis n),
      IsPauli P ∧ (∀ T ∈ S, (T : Operator (QubitBasis n)) * P = P * (T : Operator (QubitBasis n))) ∧
      compress C P = A} = ⊤ := by
  classical
  let V := Submodule.span ℂ {A : Operator (Fin K × Fin 1) | ∃ P : Operator (QubitBasis n),
    IsPauli P ∧ (∀ T ∈ S, (T : Operator (QubitBasis n)) * P = P * (T : Operator (QubitBasis n))) ∧
    compress C P = A}
  change V = ⊤
  have hspan : Submodule.span ℂ (Set.range fun p : Fin n → SinglePauli => pauliMatrix 0 p) ≤
      V.comap (compressLinear C) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change compress C (pauliMatrix 0 p) ∈ V
    have hp : IsPauli (pauliMatrix 0 p) := ⟨0, p, rfl⟩
    by_cases hc : ∀ T ∈ S, (T : Operator (QubitBasis n)) * pauliMatrix 0 p =
        pauliMatrix 0 p * (T : Operator (QubitBasis n))
    · exact Submodule.subset_span ⟨_, hp, hc, rfl⟩
    · rw [compress_zero_of_not_centralizing C S hS hspace _ hp hc]
      exact Submodule.zero_mem _
  rw [unphased_pauliMatrix_span_eq_top] at hspan
  apply top_unique
  intro A _
  obtain ⟨B, rfl⟩ := compressLinear_surjective C A
  exact hspan (show B ∈ (⊤ : Submodule ℂ (Operator (QubitBasis n))) from trivial)

#print axioms compress_trace_zero_unless_scalar
#print axioms compress_zero_of_not_centralizing
#print axioms compressed_centralizingPaulis_span

end
end CriticalDepth.FaultStabilizerLogicalTrace
