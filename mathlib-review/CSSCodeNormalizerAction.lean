import CSSCodeStabilizer

/-!
# Physical code preservation yields preservation of the CSS vector space
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open scoped Kronecker

noncomputable section

variable {n : ℕ} (H J : Submodule CSSBit (CSSWord n))

/-- The encoded subspace, expressed in computational bit coordinates. -/
def cssBinarySpace : Set (CSSWord n → ℂ) :=
  {v | (∀ a ∈ H, ∀ x, v (x + a) = v x) ∧ ∀ x, x ∉ cssOrthogonal J → v x = 0}

theorem cssEncoding_range_iff_binary (hHJ : H ≤ cssOrthogonal J) (u : QubitBasis n → ℂ) :
    u ∈ Set.range (fun w => (cssEncoding H J).mulVec w) ↔
      u ∘ (binaryWordEquiv n).symm ∈ cssBinarySpace H J := by
  let v := u ∘ (binaryWordEquiv n).symm
  have he : v ∘ binaryWordEquiv n = u :=
    funext (fun x => congrArg u ((binaryWordEquiv n).symm_apply_apply x))
  constructor
  · rintro ⟨c, hc⟩
    let b := cssLogicalEquiv H J
    let w := c ∘ b.symm
    have hb : w ∘ b = c := funext (fun i => congrArg c (b.symm_apply_apply i))
    change v ∈ cssBinarySpace H J
    rw [cssBinarySpace, ← cssCosetEncoding_range H J hHJ]
    refine ⟨w, ?_⟩
    funext x
    have h := cssEncoding_mulVec_reindex H J w ((binaryWordEquiv n).symm x)
    rw [show w ∘ cssLogicalEquiv H J = c from hb, Equiv.apply_symm_apply] at h
    exact h.symm.trans (congrFun hc _)
  · intro h
    change v ∈ cssBinarySpace H J at h
    rw [cssBinarySpace, ← cssCosetEncoding_range H J hHJ] at h
    obtain ⟨w, hw⟩ := h
    refine ⟨w ∘ cssLogicalEquiv H J, ?_⟩
    funext x
    exact (cssEncoding_mulVec_reindex H J w x).trans
      ((congrFun hw ((binaryWordEquiv n) x)).trans (congrFun he x))

/-- The physical matrix action written in the binary computational coordinates. -/
def cssBinaryAction (U : Operator (QubitBasis n)) (v : CSSWord n → ℂ) : CSSWord n → ℂ :=
  (U.mulVec (v ∘ binaryWordEquiv n)) ∘ (binaryWordEquiv n).symm

theorem cssBinaryAction_mem_space (hHJ : H ≤ cssOrthogonal J)
    (U : Operator (QubitBasis n)) (W : Operator (Fin (2 ^ cssLogicalQubits H J)))
    (hU : Implements (physicalCSSCode H J hHJ) U W)
    (v : CSSWord n → ℂ) (hv : v ∈ cssBinarySpace H J) :
    cssBinaryAction U v ∈ cssBinarySpace H J := by
  obtain ⟨_, G, _, h⟩ := hU
  have hr : v ∘ binaryWordEquiv n ∈ Set.range (fun w => (cssEncoding H J).mulVec w) := by
    apply (cssEncoding_range_iff_binary H J hHJ _).mpr
    have hcomp : (v ∘ binaryWordEquiv n) ∘ (binaryWordEquiv n).symm = v :=
      funext (fun x => congrArg v ((binaryWordEquiv n).apply_symm_apply x))
    rw [hcomp]
    exact hv
  apply (cssEncoding_range_iff_binary H J hHJ _).mp
  obtain ⟨w, hw⟩ := hr
  refine ⟨(W ⊗ₖ G).mulVec w, ?_⟩
  change U * cssEncoding H J = cssEncoding H J * (W ⊗ₖ G) at h
  change (cssEncoding H J).mulVec ((W ⊗ₖ G).mulVec w) =
    U.mulVec (v ∘ binaryWordEquiv n)
  change (cssEncoding H J).mulVec w = v ∘ binaryWordEquiv n at hw
  rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hw]

#print axioms cssBinaryAction_mem_space

end

end CriticalDepth.Manuscript20261114.CSSCode
