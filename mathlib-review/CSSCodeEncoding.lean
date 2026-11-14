import CSSCodeCosetRange

/-!
# The CSS coset isometry on the physical qubit register
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ} (H J : Submodule CSSBit (CSSWord n))

/-- Dimension of the quotient of the common Z kernel by the X checks. -/
def cssLogicalQubits : ℕ := Module.finrank CSSBit (CSSCoset H J)

theorem cssCoset_card : Fintype.card (CSSCoset H J) = 2 ^ cssLogicalQubits H J := by
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := CSSBit)]
  simp [cssLogicalQubits]

def cssLogicalEquiv : Fin (2 ^ cssLogicalQubits H J) × Fin 1 ≃ CSSCoset H J :=
  ((Equiv.prodUnique _ _).trans (finCongr (cssCoset_card H J).symm)).trans
    (Fintype.equivFin _).symm

def cssEncoding : Matrix (QubitBasis n) (Fin (2 ^ cssLogicalQubits H J) × Fin 1) ℂ :=
  fun x b => cssCosetEncoding H J (binaryWordEquiv n x) (cssLogicalEquiv H J b)

theorem cssEncoding_isometry (hHJ : H ≤ cssOrthogonal J) :
    (cssEncoding H J).conjTranspose * cssEncoding H J = 1 := by
  classical
  ext a b
  let e := cssLogicalEquiv H J
  let f (x : CSSWord n) :=
    star (cssCosetEncoding H J x (e a)) * cssCosetEncoding H J x (e b)
  change (∑ x : QubitBasis n, f (binaryWordEquiv n x)) = _
  rw [(binaryWordEquiv n).sum_comp f]
  change ((cssCosetEncoding H J).conjTranspose * cssCosetEncoding H J) (e a) (e b) = _
  rw [cssCosetEncoding_isometry H J hHJ]
  by_cases h : a = b
  · subst b
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne (fun h' => h (e.injective h')), Matrix.one_apply_ne h]

def physicalCSSCode (hHJ : H ≤ cssOrthogonal J) :
    Code n (fun _ => 2) (2 ^ cssLogicalQubits H J) 1 :=
  ⟨cssEncoding H J, cssEncoding_isometry H J hHJ⟩

theorem cssEncoding_mulVec_reindex (w : CSSCoset H J → ℂ) (x : QubitBasis n) :
    (cssEncoding H J).mulVec (w ∘ cssLogicalEquiv H J) x =
      (cssCosetEncoding H J).mulVec w (binaryWordEquiv n x) :=
  (cssLogicalEquiv H J).sum_comp
    (fun b => cssCosetEncoding H J (binaryWordEquiv n x) b * w b)

#print axioms cssCoset_card
#print axioms physicalCSSCode
#print axioms cssEncoding_mulVec_reindex

end

end CriticalDepth.Manuscript20261114.CSSCode
