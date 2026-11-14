import CSSQuadraticPhase
import CSSCodePauliChecks
import FaultOnSiteSupport

/-!
# Physical Pauli form of a translated sign monomial

The column formula with binary translation and a sign character agrees
entry by entry with the product of its physical X and Z words.
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCheckSpaces
open CriticalDepth.FaultSupportPreserving
open CriticalDepth.FaultCircuitSupport
open scoped BigOperators

variable {n : ℕ}

private theorem binaryPhaseSign_val (a : CSSBit) :
    (binaryPhaseSign a : ℂ) = cssSign a := by
  by_cases h : a = 0
  · simp [h, cssSign]
  · simp [binaryPhaseSign, cssSign, h]

private theorem binary_sum_cancel_right (x y a : CSSWord n) : x = y + a ↔ y = x + a := by
  constructor <;> intro h <;>
    rw [h, add_assoc, ZModModule.add_self, add_zero]

/-- Translation and a sign evaluated on the input column give X times Z. -/
theorem monomialTranslation_eq_smul_tensorPauli (U : Operator (QubitBasis n))
    (c p : CSSWord n) (z : ℂ)
    (hU : ∀ x y, U x y =
      if binaryWordEquiv n x = binaryWordEquiv n y + c then
        z * (binaryPhaseSign (dotProduct p (binaryWordEquiv n y)) : ℂ) else 0) :
    U = z • tensorEntries (fun i => (cssXWord c i).matrix * (cssZWord p i).matrix) := by
  rw [tensorEntries_mul, ← pauliMatrix_zero_eq_tensorEntries, ← pauliMatrix_zero_eq_tensorEntries]
  ext x y
  let f : QubitBasis n → ℂ := Pi.single y 1
  have hX' (v : QubitBasis n → ℂ) :
      (pauliMatrix 0 (cssXWord c)).mulVec v x =
        v ((binaryWordEquiv n).symm (binaryWordEquiv n x + c)) := by
    let u' : CSSWord n → ℂ := v ∘ (binaryWordEquiv n).symm
    have hcom : u' ∘ binaryWordEquiv n = v := by funext b; simp [u']
    have hh := cssXWord_mulVec c u' x
    rwa [hcom] at hh
  have hXZ := hX' ((pauliMatrix 0 (cssZWord p)).mulVec f)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, cssZWord_mulVec,
    Equiv.apply_symm_apply] at hXZ
  have heq :
      ((binaryWordEquiv n).symm (binaryWordEquiv n x + c) = y) ↔
        binaryWordEquiv n x = binaryWordEquiv n y + c := by
    rw [Equiv.symm_apply_eq]
    constructor
    · intro h
      exact (binary_sum_cancel_right (binaryWordEquiv n x) (binaryWordEquiv n y) c).mpr h.symm
    · intro h
      exact ((binary_sum_cancel_right (binaryWordEquiv n x) (binaryWordEquiv n y) c).mp h).symm
  have hEntry : (pauliMatrix 0 (cssXWord c) * pauliMatrix 0 (cssZWord p)) x y =
      cssSign (dotProduct (binaryWordEquiv n x + c) p) *
        f ((binaryWordEquiv n).symm (binaryWordEquiv n x + c)) := hXZ
  rw [hU, Matrix.smul_apply, smul_eq_mul, hEntry]
  by_cases hx : binaryWordEquiv n x = binaryWordEquiv n y + c
  · have hy := heq.mpr hx
    have hxy : binaryWordEquiv n x + c = binaryWordEquiv n y :=
      ((binary_sum_cancel_right _ _ _).mp hx).symm
    rw [if_pos hx, hy]
    have hf : f y = 1 := by simp only [f, Pi.single_eq_same]
    rw [hf, mul_one, hxy, binaryPhaseSign_val, dotProduct_comm p (binaryWordEquiv n y)]
  · have hy : (binaryWordEquiv n).symm (binaryWordEquiv n x + c) ≠ y :=
      fun hh => hx (heq.mp hh)
    have hf : f ((binaryWordEquiv n).symm (binaryWordEquiv n x + c)) = 0 := by
      simp only [f, Pi.single_eq_of_ne hy]
    rw [if_neg hx, hf, mul_zero, mul_zero]

/-- The physical Pauli product preserves every physical support. -/
theorem monomialTranslation_preservesSupports (U : Operator (QubitBasis n))
    (c p : CSSWord n) (z : ℂ)
    (hU : ∀ x y, U x y =
      if binaryWordEquiv n x = binaryWordEquiv n y + c then
        z * (binaryPhaseSign (dotProduct p (binaryWordEquiv n y)) : ℂ) else 0) :
    PreservesSupports U := by
  rw [monomialTranslation_eq_smul_tensorPauli U c p z hU]
  apply preservesSupports_smul
  apply preservesSupports_tensorEntries
  intro i
  exact isUnitary_mul (singlePauli_isUnitary (cssXWord c i))
    (singlePauli_isUnitary (cssZWord p i))

#print axioms monomialTranslation_eq_smul_tensorPauli
#print axioms monomialTranslation_preservesSupports

end
end CriticalDepth.Manuscript20261114.CSSCode
