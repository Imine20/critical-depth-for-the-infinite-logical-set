import CSSCodePauliChecks
import PauliGroup

/-!
# The CSS coset encoding is a physical Pauli stabilizer code
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.ReviewV2 CriticalDepth.PauliGroup
open scoped BigOperators

noncomputable section

variable {n : ℕ} (H J : Submodule CSSBit (CSSWord n))

private def cssPauliUnitary (p : Fin n → SinglePauli) :
    Matrix.unitaryGroup (QubitBasis n) ℂ :=
  ⟨pauliMatrix 0 p, (isUnitary_iff_mem_unitaryGroup (QubitBasis n) _).mp
    (unphased_pauliMatrix_isUnitary p)⟩

private def checkGenerators : Set (Matrix.unitaryGroup (QubitBasis n) ℂ) :=
  {U | (∃ a ∈ H, U = cssPauliUnitary (cssXWord a)) ∨
        ∃ a ∈ J, U = cssPauliUnitary (cssZWord a)}

def cssStabilizer : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ) :=
  Subgroup.closure (checkGenerators H J)

theorem exists_cssStabilizer_X (a : CSSWord n) (ha : a ∈ H) :
    ∃ U ∈ cssStabilizer H J, U.val = pauliMatrix 0 (cssXWord a) :=
  ⟨cssPauliUnitary (cssXWord a), Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩), rfl⟩

theorem exists_cssStabilizer_Z (a : CSSWord n) (ha : a ∈ J) :
    ∃ U ∈ cssStabilizer H J, U.val = pauliMatrix 0 (cssZWord a) :=
  ⟨cssPauliUnitary (cssZWord a), Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩), rfl⟩

theorem cssStabilizer_le_physicalPauliGroup :
    cssStabilizer H J ≤ physicalPauliGroup n := by
  apply (Subgroup.closure_le (physicalPauliGroup n)).mpr
  intro U hU
  change IsPauli U.val
  rcases hU with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩
  · exact ⟨0, cssXWord a, rfl⟩
  · exact ⟨0, cssZWord a, rfl⟩

private def vectorFixers (v : QubitBasis n → ℂ) :
    Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ) where
  carrier := {U | U.val.mulVec v = v}
  one_mem' := Matrix.one_mulVec _
  mul_mem' := by
    intro U W hU hW
    change U.val.mulVec v = v at hU
    change W.val.mulVec v = v at hW
    change (U.val * W.val).mulVec v = v
    rw [← Matrix.mulVec_mulVec, hW, hU]
  inv_mem' := by
    intro U hU
    change U.val.mulVec v = v at hU
    have hunit : star U.val * U.val = 1 :=
      ((isUnitary_iff_mem_unitaryGroup (QubitBasis n) U.val).mpr U.property).1
    change (star U.val).mulVec v = v
    calc
      (star U.val).mulVec v = (star U.val).mulVec (U.val.mulVec v) := by rw [hU]
      _ = v := by rw [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]

private theorem cssStabilizer_fixed_iff (v : CSSWord n → ℂ) :
    (∀ U ∈ cssStabilizer H J,
        U.val.mulVec (v ∘ binaryWordEquiv n) = v ∘ binaryWordEquiv n) ↔
      (∀ a ∈ H, ∀ x, v (x + a) = v x) ∧ ∀ x, x ∉ cssOrthogonal J → v x = 0 := by
  constructor
  · intro h
    refine ⟨(cssPhysicalX_fixed_iff H v).mp ?_, (cssPhysicalZ_fixed_iff J v).mp ?_⟩
    · intro a ha
      exact h (cssPauliUnitary (cssXWord a)) (Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩))
    · intro a ha
      exact h (cssPauliUnitary (cssZWord a)) (Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩))
  · rintro ⟨hx, hz⟩
    have hX := (cssPhysicalX_fixed_iff H v).mpr hx
    have hZ := (cssPhysicalZ_fixed_iff J v).mpr hz
    apply (show cssStabilizer H J ≤ vectorFixers (v ∘ binaryWordEquiv n) from ?_)
    apply (Subgroup.closure_le (vectorFixers (v ∘ binaryWordEquiv n))).mpr
    intro U hU
    change U.val.mulVec (v ∘ binaryWordEquiv n) = v ∘ binaryWordEquiv n
    rcases hU with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact hX a ha
    · exact hZ a ha

theorem cssEncoding_range_eq_stabilizer (hHJ : H ≤ cssOrthogonal J) :
    Set.range (fun w => (cssEncoding H J).mulVec w) =
      {v | ∀ U ∈ cssStabilizer H J, U.val.mulVec v = v} := by
  let e := binaryWordEquiv n
  ext u
  let v := u ∘ e.symm
  have he : v ∘ e = u := by
    funext x
    exact congrArg u (e.symm_apply_apply x)
  have hfix := cssStabilizer_fixed_iff H J v
  rw [he] at hfix
  change u ∈ Set.range (fun w => (cssEncoding H J).mulVec w) ↔
    (∀ U ∈ cssStabilizer H J, U.val.mulVec u = u)
  rw [hfix]
  change _ ↔ v ∈ {v | (∀ a ∈ H, ∀ x, v (x + a) = v x) ∧
    ∀ x, x ∉ cssOrthogonal J → v x = 0}
  rw [← cssCosetEncoding_range H J hHJ]
  constructor
  · rintro ⟨c, hc⟩
    let b := cssLogicalEquiv H J
    let w := c ∘ b.symm
    have hb : w ∘ b = c := by
      funext i
      exact congrArg c (b.symm_apply_apply i)
    refine ⟨w, ?_⟩
    funext x
    have h := cssEncoding_mulVec_reindex H J w (e.symm x)
    change (cssEncoding H J).mulVec (w ∘ b) (e.symm x) =
      (cssCosetEncoding H J).mulVec w (e (e.symm x)) at h
    rw [hb, Equiv.apply_symm_apply] at h
    exact h.symm.trans (congrFun hc (e.symm x))
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ cssLogicalEquiv H J, ?_⟩
    funext x
    exact (cssEncoding_mulVec_reindex H J w x).trans
      ((congrFun hw (e x)).trans (congrFun he x))

theorem physicalCSSCode_isStabilizer (hHJ : H ≤ cssOrthogonal J) :
    IsStabilizer (physicalCSSCode H J hHJ) :=
  ⟨cssStabilizer H J, fun _ hU => cssStabilizer_le_physicalPauliGroup H J hU,
    cssEncoding_range_eq_stabilizer H J hHJ⟩

theorem cssEncoding_xCheck_fixes (hHJ : H ≤ cssOrthogonal J)
    (a : CSSWord n) (ha : a ∈ H) :
    pauliMatrix 0 (cssXWord a) * cssEncoding H J = cssEncoding H J :=
  encoding_fixed_of_fixedSpace (physicalCSSCode H J hHJ) _ (cssEncoding_range_eq_stabilizer H J hHJ)
    (cssPauliUnitary (cssXWord a)) (Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩))

theorem cssEncoding_zCheck_fixes (hHJ : H ≤ cssOrthogonal J)
    (a : CSSWord n) (ha : a ∈ J) :
    pauliMatrix 0 (cssZWord a) * cssEncoding H J = cssEncoding H J :=
  encoding_fixed_of_fixedSpace (physicalCSSCode H J hHJ) _ (cssEncoding_range_eq_stabilizer H J hHJ)
    (cssPauliUnitary (cssZWord a)) (Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩))

#print axioms physicalCSSCode_isStabilizer
#print axioms cssEncoding_xCheck_fixes
#print axioms cssEncoding_zCheck_fixes

end

end CriticalDepth.Manuscript20261114.CSSCode
