import StabilizerLogicalFrame
import StabilizerCosetSelection

/-!
# Unphased representatives at minimum stabilizer coset weight
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix
open scoped Kronecker

noncomputable section

variable {n k : ℕ}
variable (C : Code n (fun _ => 2) (2^k) 1)
variable (S : PhysicalStabilizer n) (hS : ∀ U ∈ S, IsPauli U.val)
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
  {v | ∀ U ∈ S, U.val.mulVec v = v})

include hS hspace in
private theorem fix_space_stabilizer_selfAdjoint (U : Matrix.unitaryGroup (QubitBasis n) ℂ)
    (hU : U ∈ S) : star U.val = U.val := by
  obtain ⟨a,p,ha⟩ := hS U hU
  let c := (Complex.I ^ a.val)^2
  have hsq : U.val * U.val = c • (1 : Operator (QubitBasis n)) := by
    rw [ha, pauliMatrix_eq_phase_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, unphased_pauliMatrix_sq]
    change (Complex.I ^ a.val * Complex.I ^ a.val) • (1 : Operator (QubitBasis n)) =
      ((Complex.I ^ a.val)^2) • 1
    rw [pow_two]
  have hfix := encoding_fixed_of_fixedSpace C S hspace U hU
  have h := congrArg (fun M : Operator (QubitBasis n) => C.encoding.conjTranspose * (M * C.encoding)) hsq
  change C.encoding.conjTranspose * ((U.val * U.val) * C.encoding) =
    C.encoding.conjTranspose * ((c • (1 : Operator (QubitBasis n))) * C.encoding) at h
  rw [Matrix.mul_assoc U.val, hfix, hfix, C.isometry, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, C.isometry] at h
  let i : Fin (2^k) × Fin 1 := (⟨0,by positivity⟩,0)
  have h₁ : c = 1 := by
    have he := congrArg (fun A : Operator (Fin (2^k) × Fin 1) => A i i) h.symm
    simpa [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul] using he
  rw [h₁, one_smul] at hsq
  calc
    star U.val = star U.val * (U.val * U.val) := by rw [hsq, Matrix.mul_one]
    _ = U.val := by rw [← Matrix.mul_assoc, show star U.val * U.val = 1 from U.property.1, Matrix.one_mul]

include hS hspace in
/-- Minimum support is evaluated in the right stabilizer coset, and the
unphased word keeps the intended logical direction up to real sign. -/
theorem exists_min_unphased_stabilizer_rep (p : Fin n → SinglePauli) (A : Operator (Fin (2^k)))
    (hc : ∀ U ∈ S, U.val * pauliMatrix 0 p = pauliMatrix 0 p * U.val)
    (hA : pauliMatrix 0 p * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin 1)))) :
    ∃ q ∈ stabilizerCosetLabels S (0,p),
      (∀ r ∈ stabilizerCosetLabels S (0,p), (pauliSupport q.2).card ≤ (pauliSupport r.2).card) ∧
      ((pauliMatrix 0 q.2 * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin 1)))) ∨
       (pauliMatrix 0 q.2 * C.encoding = C.encoding * ((-A) ⊗ₖ (1 : Operator (Fin 1))))) := by
  obtain ⟨q,hq,hmin⟩ := exists_min_weight_stabilizer_coset_label S (0,p)
  refine ⟨q,hq,hmin,?_⟩
  have he := (stabilizerCosetLabel_encoding C S hspace hq).trans hA
  obtain ⟨U,hU,hqU⟩ := hq
  change pauliMatrix q.1 q.2 = pauliMatrix 0 p * U.val at hqU
  have hqself : star (pauliMatrix q.1 q.2) = pauliMatrix q.1 q.2 := by
    rw [hqU, star_mul, fix_space_stabilizer_selfAdjoint C S hS hspace U hU,
      show star (pauliMatrix 0 p) = pauliMatrix 0 p from unphased_pauliMatrix_selfAdjoint p]
    exact hc U hU
  rcases pauli_hermitian_phase hqself with hp | hp
  · exact Or.inl (by simpa only [hp] using he)
  · right
    rw [hp, Matrix.neg_mul] at he
    have hh := congrArg Neg.neg he
    rw [neg_neg, ← Matrix.mul_neg] at hh
    have hK : -(A ⊗ₖ (1 : Operator (Fin 1))) = (-A) ⊗ₖ (1 : Operator (Fin 1)) := by
      ext a b
      simp [Matrix.kronecker_apply, Matrix.neg_apply]
    rwa [hK] at hh

#print axioms exists_min_unphased_stabilizer_rep

end

end CriticalDepth.Manuscript20261114
