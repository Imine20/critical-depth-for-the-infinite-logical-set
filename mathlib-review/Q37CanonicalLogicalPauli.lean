import Q37CanonicalEncoding

/-!
# The ordered Q37 logical Z and its bare physical representative
-/

open scoped BigOperators Kronecker Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCode Matrix
open CriticalDepth.FaultShorSaturation

noncomputable section

set_option maxRecDepth 4096 in
theorem q37CanonicalCode_logicalZ :
    pauliMatrix 0 (cssZWord q37LogicalZ) * q37CanonicalCode.encoding =
      q37CanonicalCode.encoding * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin 1))) := by
  have hD : SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin 1)) =
      Matrix.diagonal (fun b : Fin 2 × Fin 1 => if b.1 = 0 then (1 : ℂ) else -1) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    have h : a = b := Subsingleton.elim _ _
    subst b
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply, SinglePauli.matrix]
  rw [hD]
  ext x b
  rw [Matrix.mul_diagonal]
  change (pauliMatrix 0 (cssZWord q37LogicalZ)).mulVec
      (fun y => q37CanonicalEncoding y b) x =
      q37CanonicalEncoding x b * (if b.1 = 0 then 1 else -1)
  rw [cssZWord_mulVec]
  by_cases h : q37CanonicalEncoding x b = 0
  · simp [h]
  · obtain ⟨v, hv⟩ := q37Canonical_nonzero_word x b h
    have hc : v ᵥ* checkMatrix xChecks ∈ q37XChecks := ⟨v, rfl⟩
    have hd : dotProduct (v ᵥ* checkMatrix xChecks) q37LogicalZ = 0 := by
      rw [dotProduct_comm]
      exact q37LogicalZ_in_dual _ hc
    rw [hv, add_dotProduct, hd, zero_add]
    by_cases hb : b.1 = 0
    · simp [hb, cssSign]
    · simp [hb, cssSign, q37Logical_dot]

#print axioms q37CanonicalCode_logicalZ

end

end CriticalDepth.Q37BinaryData
