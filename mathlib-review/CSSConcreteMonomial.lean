import CSSPhysicalCheckClassification
import CSSShortDualTests
import CSSCodeDistance

/-!
# Physical monomial rigidity for the concrete CSS coset code

Short dual X words generate all Z checks needed by the monomiality
argument. The distance assumptions are those used for that step of
the manuscript's rigidity proof.
-/

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCheckSpaces
open CriticalDepth.Manuscript20261114.CSSZConjugation

variable {n : ℕ}

/-- Z checks indexed by short words generate the Z check of every word in
the dual of the X-check space. -/
theorem zCheck_mem_adjoin_short_dual (H : Submodule CSSBit (CSSWord n))
    (v : CSSWord n) (hv : v ∈ cssOrthogonal H) :
    zCheck v ∈ Algebra.adjoin ℂ (zCheck '' (cssShortOrthogonalityTests H).tests) := by
  classical
  let S := (cssShortOrthogonalityTests H).tests
  let D := Algebra.adjoin ℂ (zCheck '' S)
  have hzero : zCheck (0 : CSSWord n) = 1 := cssPureZ_zero
  have hadd (a b : CSSWord n) : zCheck (a + b) = zCheck a * zCheck b :=
    (cssPureZ_add a b).symm
  have hT : v ∈ Submodule.span CSSBit S := by
    change v ∈ Submodule.span CSSBit {v : CSSWord n | v ∈ cssOrthogonal H ∧
      wordWeight v ≤ Module.finrank CSSBit H + 1}
    rw [span_short_cssOrthogonal_words H]
    exact hv
  change zCheck v ∈ D
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hT
  · intro w hw
    exact Algebra.subset_adjoin ⟨w, hw, rfl⟩
  · rw [hzero]
    exact D.one_mem
  · intro x y _ _ hx hy
    rw [hadd]
    exact D.mul_mem hx hy
  · intro a w _ hw
    have ha : a = 0 ∨ a = 1 := by decide +revert
    rcases ha with rfl | rfl
    · rw [zero_smul, hzero]
      exact D.one_mem
    · rwa [one_smul]

/-- A pure Z word orthogonal to the X checks acts diagonally on the
encoded coset basis. -/
theorem zCheck_encoded_preserving
    (H J : Submodule CSSBit (CSSWord n)) (v : CSSWord n) (hv : v ∈ cssOrthogonal H) :
    ∃ F : Operator (Fin (2 ^ cssLogicalQubits H J) × Fin 1),
      zCheck v * cssEncoding H J = cssEncoding H J * F := by
  classical
  let preimage (b : Fin (2 ^ cssLogicalQubits H J) × Fin 1) :=
    cosetRepresentative H J (cssLogicalEquiv H J b)
  have hpreimage (b : Fin (2 ^ cssLogicalQubits H J) × Fin 1) :
      (insideChecks H J).mkQ (preimage b) = cssLogicalEquiv H J b :=
    cosetRepresentative_mk H J (cssLogicalEquiv H J b)
  refine ⟨Matrix.diagonal (fun b => cssSign (dotProduct (preimage b).val v)), ?_⟩
  ext x b
  rw [Matrix.mul_diagonal]
  have h := cssZWord_logical_sign H J v hv (preimage b) x
  have hb : (cssLogicalEquiv H J).symm ((insideChecks H J).mkQ (preimage b)) = b := by
    rw [hpreimage, Equiv.symm_apply_apply]
  change (pauliMatrix 0 (cssZWord v) * cssEncoding H J) x
    ((cssLogicalEquiv H J).symm ((insideChecks H J).mkQ (preimage b))) =
      cssSign (dotProduct (preimage b).val v) * cssEncoding H J x
        ((cssLogicalEquiv H J).symm ((insideChecks H J).mkQ (preimage b))) at h
  rw [hb] at h
  exact h.trans (mul_comm _ _)

/-- A short physical circuit preserving the actual CSS coset code has a
monomial matrix when the primal check spaces have no short words and the
dual of J has no short nonzero X mask. -/
theorem physicalCSS_exactCircuit_monomial
    (H J : Submodule CSSBit (CSSWord n)) (hHJ : H ≤ cssOrthogonal J)
    (ρ R : ℕ) (hρ : 1 ≤ ρ)
    (hH : ∀ v ∈ H, v ≠ 0 → R < wordWeight v)
    (hHlarge : ∀ v ∈ H, v ≠ 0 → R * (Module.finrank CSSBit H + 1) < wordWeight v)
    (hJlarge : ∀ v ∈ J, v ≠ 0 → R * (Module.finrank CSSBit H + 1) < wordWeight v)
    (hJdual : ∀ v ∈ cssOrthogonal J, v ≠ 0 → R * (Module.finrank CSSBit H + 1) < wordWeight v)
    (L : List (Layer n (fun _ => 2) ρ)) (hR : ρ ^ L.length ≤ R)
    (W : Operator (Fin (2 ^ cssLogicalQubits H J)))
    (hW : Implements (physicalCSSCode H J hHJ) (layerSequenceEval L) W) :
    ∃ (f : Equiv.Perm (QubitBasis n)) (phase : QubitBasis n → ℂ),
      (∀ j, star (phase j) * phase j = 1) ∧
      ∀ x j, layerSequenceEval L x j = if x = f j then phase j else 0 := by
  let C := physicalCSSCode H J hHJ
  let S := cssStabilizer H J
  let B := Module.finrank CSSBit H + 1
  let tests := cssShortOrthogonalityTests H
  have hSpace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v} := by
    change Set.range (fun v => (cssEncoding H J).mulVec v) =
      {v | ∀ U ∈ cssStabilizer H J, (U : Operator (QubitBasis n)).mulVec v = v}
    exact cssEncoding_range_eq_stabilizer H J hHJ
  have hCheck : ∀ v ∈ tests.tests, ∃ F : Operator (Fin (2 ^ cssLogicalQubits H J) × Fin 1),
      zCheck v * C.encoding = C.encoding * F := by
    intro v hv
    exact zCheck_encoded_preserving H J v hv.1
  have hNoShort : ∀ (A : Finset (Fin n)), A.card ≤ R * B →
      ∀ U ∈ S, SupportedOn (U : Operator (QubitBasis n)) A → U = 1 :=
    css_no_short_stabilizer (H := H) (J := J) hHJ (B := R * B) hHlarge hJlarge
  have hLocal : ∀ (A : Finset (Fin n)), A.card ≤ R * B → ∀ p : A → SinglePauli,
      (∀ U ∈ S, (U : Operator (QubitBasis n)) * pauliMatrix 0 (extendLocalPauli A p) =
          pauliMatrix 0 (extendLocalPauli A p) * (U : Operator (QubitBasis n))) →
      pauliMatrix 0 (extendLocalPauli A p) ∈ Algebra.adjoin ℂ (zCheck '' tests.tests) := by
    intro A hA p hp
    obtain ⟨v, hv, hP⟩ := css_local_centralizer_eq_zCheck (H := H) (J := J) hJdual A hA p hp
    rw [hP]
    exact zCheck_mem_adjoin_short_dual H v hv
  exact exists_monomial_of_css_check_structure (n := n) (k := cssLogicalQubits H J)
    (ρ := ρ) (R := R) (D := B) C S
    (fun U hu => cssStabilizer_le_physicalPauliGroup H J hu)
    hSpace H tests hCheck hH hNoShort hLocal L hρ hR W hW

#print axioms zCheck_mem_adjoin_short_dual
#print axioms zCheck_encoded_preserving
#print axioms physicalCSS_exactCircuit_monomial

end CriticalDepth.Manuscript20261114.CSSCode
