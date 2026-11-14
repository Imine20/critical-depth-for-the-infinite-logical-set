import CSSCodePauliMasks

/-!
# Actual distance of the manuscript's CSS coset code

A low-weight Pauli either anticommutes with a check and has zero
compression, or has both masks zero by the dual-distance bounds.
A weight-d Z word in the X dual outside the Z check space acts with
opposite signs on two encoded cosets.
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open scoped BigOperators Kronecker

noncomputable section

variable {n d : ℕ} (H J : Submodule CSSBit (CSSWord n))
variable (hHJ : H ≤ cssOrthogonal J)

theorem cssSmallPauli_detected
    (hH : ∀ w ∈ cssOrthogonal H, w ≠ 0 → d ≤ CSSCheckSpaces.wordWeight w)
    (hJ : ∀ w ∈ cssOrthogonal J, w ≠ 0 → d ≤ CSSCheckSpaces.wordWeight w)
    (p : Fin n → SinglePauli) (hp : (pauliSupport p).card < d) :
    GaugeOnly (physicalCSSCode H J hHJ) (pauliMatrix 0 p) := by
  classical
  let C := physicalCSSCode H J hHJ
  change GaugeOnly C _
  by_cases hx : cssMaskX p ∈ cssOrthogonal J
  · by_cases hz : cssMaskZ p ∈ cssOrthogonal H
    · have hx0 : cssMaskX p = 0 := by
        by_contra hx'
        exact (not_le_of_gt hp) ((hJ _ hx hx').trans (cssMaskX_weight_le p))
      have hz0 : cssMaskZ p = 0 := by
        by_contra hz'
        exact (not_le_of_gt hp) ((hH _ hz hz').trans (cssMaskZ_weight_le p))
      rw [eq_identity_of_zero_cssMasks p hx0 hz0]
      refine ⟨1, ?_⟩
      rw [Matrix.mul_one, C.isometry, Matrix.one_kronecker_one]
    · change ¬ ∀ a ∈ H, dotProduct (cssMaskZ p) a = 0 at hz
      push Not at hz
      obtain ⟨a, ha, hne⟩ := hz
      have hanti := cssX_commutation a p
      simp only [cssSign, ite_eq_right hne, neg_one_smul] at hanti
      exact anticommuting_fixed_operator_gaugeOnly C _ _
        (unphased_pauliMatrix_isUnitary _) (cssEncoding_xCheck_fixes H J hHJ a ha) hanti
  · change ¬ ∀ a ∈ J, dotProduct (cssMaskX p) a = 0 at hx
    push Not at hx
    obtain ⟨a, ha, hne⟩ := hx
    have hanti := cssZ_commutation a p
    simp only [cssSign, ite_eq_right hne, neg_one_smul] at hanti
    exact anticommuting_fixed_operator_gaugeOnly C _ _
      (unphased_pauliMatrix_isUnitary _) (cssEncoding_zCheck_fixes H J hHJ a ha) hanti

theorem physicalCSSCode_detectsBelow
    (hH : ∀ w ∈ cssOrthogonal H, w ≠ 0 → d ≤ CSSCheckSpaces.wordWeight w)
    (hJ : ∀ w ∈ cssOrthogonal J, w ≠ 0 → d ≤ CSSCheckSpaces.wordWeight w) :
    DetectsBelow (physicalCSSCode H J hHJ) d := by
  classical
  let C := physicalCSSCode H J hHJ
  intro S hS O hO
  obtain ⟨A, hA⟩ := hO
  let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin n => 2) S)) :=
    (gaugeOnlyComplexSubmodule C).comap (localEmbedLinearMap S)
  have hspan : pauliTensorSpan S ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change GaugeOnly C (localEmbed S (tensorPauli p))
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    apply cssSmallPauli_detected H J hHJ hH hJ
    have hsub : pauliSupport (extendLocalPauli S p) ⊆ S := by
      apply pauliSupport_subset_of_outside_identity
      intro i hi
      simp [extendLocalPauli, hi]
    exact (Finset.card_le_card hsub).trans_lt hS
  rw [tensorPauli_span_eq_top] at hspan
  have hAB : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
  change GaugeOnly C (localEmbed S A) at hAB
  simpa only [hA] using hAB

private theorem cssZ_constant_on_coset (z : CSSWord n) (hz : z ∈ cssOrthogonal H)
    (b : CSSCoset H J) (x : CSSWord n) (hx : x ∈ cosetWords H J b) :
    dotProduct x z = dotProduct (cosetRepresentative H J b).val z := by
  obtain ⟨hx', hb⟩ := (mem_cosetWords H J b x).mp hx
  let u : cssOrthogonal J := ⟨x, hx'⟩
  let r := cosetRepresentative H J b
  have hq : (insideChecks H J).mkQ (u - r) = 0 := by
    rw [map_sub, cosetRepresentative_mk]
    exact sub_eq_zero.mpr hb
  have hInside : u - r ∈ insideChecks H J :=
    (Submodule.Quotient.mk_eq_zero (insideChecks H J)).mp hq
  have hH : x - r.val ∈ H := hInside
  have hh : dotProduct (x - r.val) z = 0 := by
    rw [dotProduct_comm]
    exact (cssOrthogonal_mem H z).mp hz _ hH
  have he : dotProduct (x - r.val) z = dotProduct x z - dotProduct r.val z := by
    simp [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [he] at hh
  exact sub_eq_zero.mp hh

theorem cssZWord_logical_sign (z : CSSWord n) (hz : z ∈ cssOrthogonal H)
    (x : cssOrthogonal J) :
    ∀ w : QubitBasis n, let b := (cssLogicalEquiv H J).symm ((insideChecks H J).mkQ x)
      (pauliMatrix 0 (cssZWord z) * cssEncoding H J) w b =
        cssSign (dotProduct x.val z) * cssEncoding H J w b := by
  intro w b
  classical
  change (pauliMatrix 0 (cssZWord z)).mulVec (fun y => cssEncoding H J y b) w = _
  rw [cssZWord_mulVec]
  let k := (insideChecks H J).mkQ x
  have hk : cssLogicalEquiv H J b = k := (cssLogicalEquiv H J).apply_symm_apply k
  change cssSign (dotProduct (binaryWordEquiv n w) z) *
      cssCosetEncoding H J (binaryWordEquiv n w) (cssLogicalEquiv H J b) =
    cssSign (dotProduct x.val z) *
      cssCosetEncoding H J (binaryWordEquiv n w) (cssLogicalEquiv H J b)
  rw [hk]
  by_cases hw : binaryWordEquiv n w ∈ cosetWords H J k
  · rw [cssZ_constant_on_coset H J z hz k _ hw,
      cssZ_constant_on_coset H J z hz k x.val (cosetWords_mem_mk H J x)]
  · simp [cssCosetEncoding, hw]

theorem cssZWord_nongauge (z : CSSWord n) (hz : z ∈ cssOrthogonal H) (hzJ : z ∉ J) :
    ¬ GaugeOnly (physicalCSSCode H J hHJ) (pauliMatrix 0 (cssZWord z)) := by
  let C := physicalCSSCode H J hHJ
  obtain ⟨x, hx, hs⟩ := exists_orthogonal_dot_one J z hzJ
  rintro ⟨M, hM⟩
  have hdiag (a : cssOrthogonal J) :
      cssSign (dotProduct a.val z) = M 0 0 := by
    let b := (cssLogicalEquiv H J).symm ((insideChecks H J).mkQ a)
    have hcol (w : QubitBasis n) :
        (pauliMatrix 0 (cssZWord z) * C.encoding) w b =
          cssSign (dotProduct a.val z) * C.encoding w b :=
      cssZWord_logical_sign H J z hz a w
    have hnorm := congrArg (fun A => A b b) C.isometry
    change (∑ w, star (C.encoding w b) * C.encoding w b) =
      (1 : Operator (Fin (2 ^ cssLogicalQubits H J) × Fin 1)) b b at hnorm
    rw [Matrix.one_apply_eq] at hnorm
    have h := congrArg (fun A => A b b) hM
    rw [Matrix.mul_assoc] at h
    change (∑ w, star (C.encoding w b) *
      (pauliMatrix 0 (cssZWord z) * C.encoding) w b) =
      ((1 : Operator (Fin (2 ^ cssLogicalQubits H J))) ⊗ₖ M) b b at h
    simp only [hcol] at h
    have hb : b.2 = 0 := Subsingleton.elim _ _
    have hright : (((1 : Operator (Fin (2 ^ cssLogicalQubits H J))) ⊗ₖ M) b b) = M 0 0 := by
      rw [Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul, hb]
    rw [hright] at h
    calc
      cssSign (dotProduct a.val z) = cssSign (dotProduct a.val z) *
          ∑ w, star (C.encoding w b) * C.encoding w b := by rw [hnorm, mul_one]
      _ = ∑ w, star (C.encoding w b) *
          (cssSign (dotProduct a.val z) * C.encoding w b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = M 0 0 := h
  have h₀ : (1 : ℂ) = M 0 0 := by simpa [cssSign] using hdiag 0
  have h₁ : (-1 : ℂ) = M 0 0 := by
    have hm := hdiag ⟨x, hx⟩
    simpa [hs, cssSign] using hm
  have hbad : (1 : ℂ) = -1 := h₀.trans h₁.symm
  norm_num at hbad

theorem physicalCSSCode_hasActualDistance
    (hH : ∀ w ∈ cssOrthogonal H, w ≠ 0 → d ≤ CSSCheckSpaces.wordWeight w)
    (hJ : ∀ w ∈ cssOrthogonal J, w ≠ 0 → d ≤ CSSCheckSpaces.wordWeight w)
    (z : CSSWord n) (hz : z ∈ cssOrthogonal H) (hzJ : z ∉ J)
    (hweight : CSSCheckSpaces.wordWeight z = d) :
    HasActualDistance (physicalCSSCode H J hHJ) d := by
  exact ⟨physicalCSSCode_detectsBelow H J hHJ hH hJ, pauliSupport (cssZWord z),
    (cssZWord_support_card z).trans hweight, pauliMatrix 0 (cssZWord z),
    pauliMatrix_supportedOn_pauliSupport (cssZWord z), cssZWord_nongauge H J hHJ z hz hzJ⟩

#print axioms physicalCSSCode_detectsBelow
#print axioms physicalCSSCode_hasActualDistance

end

end CriticalDepth.Manuscript20261114.CSSCode
