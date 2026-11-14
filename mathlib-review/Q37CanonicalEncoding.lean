import Q37CheckSpaces

/-!
# Ordered CSS coset encodings with one logical bit
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.FaultShorSaturation

noncomputable section

variable {n : ℕ}
variable (H J : Submodule CSSBit (CSSWord n)) {k : CSSWord n}
variable (hk : k ∈ cssOrthogonal J)

def logicalRepresentative (b : Fin 2 × Fin 1) : cssOrthogonal J :=
  if b.1 = 0 then 0 else ⟨k, hk⟩

def logicalCoset (b : Fin 2 × Fin 1) : CSSCoset H J :=
  (insideChecks H J).mkQ (logicalRepresentative J hk b)

private theorem logicalCoset_injective (hn : k ∉ H) : Function.Injective (logicalCoset H J hk) := by
  intro a b hab
  apply Prod.ext
  · by_contra h
    have h01 (x y : Fin 2) : x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
      decide +revert
    have he : (insideChecks H J).mkQ (⟨k, hk⟩ : cssOrthogonal J) = 0 := by
      rcases h01 a.1 b.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simpa [logicalCoset, logicalRepresentative, ha, hb] using hab.symm
      · simpa [logicalCoset, logicalRepresentative, ha, hb] using hab
    exact hn ((Submodule.Quotient.mk_eq_zero (insideChecks H J)).mp he)
  · exact Subsingleton.elim _ _

/-- The two quotient classes indexed by the zero and logical-X representatives. -/
def logicalCosetEquiv (hn : k ∉ H) (hDim : cssLogicalQubits H J = 1) :
    Fin 2 × Fin 1 ≃ CSSCoset H J :=
  Equiv.ofBijective (logicalCoset H J hk)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨logicalCoset_injective H J hk hn, by
      rw [cssCoset_card, hDim]
      decide⟩)

def orderedCSSEncoding : Matrix (QubitBasis n) (Fin 2 × Fin 1) ℂ :=
  fun x b => cssCosetEncoding H J (binaryWordEquiv n x) (logicalCoset H J hk b)

theorem orderedCSSEncoding_isometry (hHJ : H ≤ cssOrthogonal J)
    (hn : k ∉ H) (hDim : cssLogicalQubits H J = 1) :
    (orderedCSSEncoding H J hk).conjTranspose * orderedCSSEncoding H J hk = 1 := by
  classical
  let e := logicalCosetEquiv H J hk hn hDim
  ext a b
  let f (x : CSSWord n) := star (cssCosetEncoding H J x (e a)) *
    cssCosetEncoding H J x (e b)
  change (∑ x : QubitBasis n, f (binaryWordEquiv n x)) = _
  rw [(binaryWordEquiv n).sum_comp f]
  change ((cssCosetEncoding H J).conjTranspose * cssCosetEncoding H J) (e a) (e b) = _
  rw [cssCosetEncoding_isometry H J hHJ]
  by_cases h : a = b
  · subst b
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne (fun he => h (e.injective he)), Matrix.one_apply_ne h]

/-- Nonzero entries are precisely the translates of the X-check words by
the selected logical representative. -/
theorem orderedCSSEncoding_nonzero_word (x : QubitBasis n) (b : Fin 2 × Fin 1)
    (hx : orderedCSSEncoding H J hk x b ≠ 0) :
    ∃ v ∈ H, binaryWordEquiv n x = v + (logicalRepresentative J hk b).val := by
  let r := logicalRepresentative J hk b
  have hmem : binaryWordEquiv n x ∈ cosetWords H J (logicalCoset H J hk b) := by
    by_contra h
    exact hx (by simp [orderedCSSEncoding, cssCosetEncoding, h])
  obtain ⟨hw, hwq⟩ := (mem_cosetWords H J _ _).mp hmem
  let a : cssOrthogonal J := ⟨binaryWordEquiv n x, hw⟩
  have he : (insideChecks H J).mkQ a = (insideChecks H J).mkQ r := hwq
  have hH : a - r ∈ insideChecks H J := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (insideChecks H J).mkQ (a - r) = 0
    rw [map_sub, he, sub_self]
  change a.val - r.val ∈ H at hH
  exact ⟨a.val - r.val, hH, (sub_add_cancel a.val r.val).symm⟩

theorem q37SwappedLogicalQubits : cssLogicalQubits q37ZChecks q37XChecks = 1 := by
  rw [cssLogicalQubits_eq_sub _ _ (cssChecksCompatible_symm.mp q37ChecksCompatible),
    q37XChecks_finrank, q37ZChecks_finrank]

def q37CanonicalEncoding : Matrix (QubitBasis 37) (Fin 2 × Fin 1) ℂ :=
  orderedCSSEncoding q37XChecks q37ZChecks q37LogicalX_in_dual

def q37DualEncoding : Matrix (QubitBasis 37) (Fin 2 × Fin 1) ℂ :=
  orderedCSSEncoding q37ZChecks q37XChecks q37LogicalZ_in_dual

theorem q37CanonicalEncoding_isometry :
    q37CanonicalEncoding.conjTranspose * q37CanonicalEncoding = 1 :=
  orderedCSSEncoding_isometry q37XChecks q37ZChecks q37LogicalX_in_dual
    q37ChecksCompatible q37LogicalX_not_check q37LogicalQubits

theorem q37DualEncoding_isometry :
    q37DualEncoding.conjTranspose * q37DualEncoding = 1 :=
  orderedCSSEncoding_isometry q37ZChecks q37XChecks q37LogicalZ_in_dual
    (cssChecksCompatible_symm.mp q37ChecksCompatible) q37LogicalZ_not_check q37SwappedLogicalQubits

def q37CanonicalCode : Code 37 (fun _ => 2) 2 1 :=
  ⟨q37CanonicalEncoding, q37CanonicalEncoding_isometry⟩

theorem q37Canonical_nonzero_word (x : QubitBasis 37) (b : Fin 2 × Fin 1)
    (hx : q37CanonicalEncoding x b ≠ 0) :
    ∃ v : Fin xChecks.length → CSSBit,
      binaryWordEquiv 37 x = v ᵥ* checkMatrix xChecks + if b.1 = 0 then 0 else q37LogicalX := by
  obtain ⟨v, hv, hw⟩ := orderedCSSEncoding_nonzero_word _ _ q37LogicalX_in_dual x b hx
  obtain ⟨c, rfl⟩ := hv
  exact ⟨c, by by_cases h : b.1 = 0 <;> simpa [logicalRepresentative, h] using hw⟩

theorem q37Dual_nonzero_word (x : QubitBasis 37) (b : Fin 2 × Fin 1)
    (hx : q37DualEncoding x b ≠ 0) :
    ∃ v : Fin zChecks.length → CSSBit,
      binaryWordEquiv 37 x = v ᵥ* checkMatrix zChecks + if b.1 = 0 then 0 else q37LogicalZ := by
  obtain ⟨v, hv, hw⟩ := orderedCSSEncoding_nonzero_word _ _ q37LogicalZ_in_dual x b hx
  obtain ⟨c, rfl⟩ := hv
  exact ⟨c, by by_cases h : b.1 = 0 <;> simpa [logicalRepresentative, h] using hw⟩

#print axioms orderedCSSEncoding_isometry
#print axioms q37CanonicalEncoding_isometry
#print axioms q37DualEncoding_isometry
#print axioms q37Canonical_nonzero_word
#print axioms q37Dual_nonzero_word

end

end CriticalDepth.Q37BinaryData
