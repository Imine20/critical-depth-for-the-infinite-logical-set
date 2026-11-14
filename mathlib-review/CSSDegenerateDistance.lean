import CSSCodeDistance

/-!
# Distance detection in degenerate CSS codes

A commuting low-weight word can have nonzero masks. It is detected
because each low mask then lies in its own check space, and their
ordered product fixes the encoded vectors up to a scalar.
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript
open scoped BigOperators Kronecker

variable {n d : ℕ}

private def xzPhase (p : SinglePauli) : ℂ := if p = .Y then Complex.I else 1

private theorem single_eq_CSSXZ (p : SinglePauli) :
    p.matrix = xzPhase p •
      ((cssXWord (cssMaskX (fun _ : Fin 1 => p)) 0).matrix *
        (cssZWord (cssMaskZ (fun _ : Fin 1 => p)) 0).matrix) := by
  have hx : cssXWord (cssMaskX (fun _ : Fin 1 => p)) 0 =
      (match p with | .X | .Y => SinglePauli.X | _ => SinglePauli.I) := by
    cases p <;> rfl
  have hz : cssZWord (cssMaskZ (fun _ : Fin 1 => p)) 0 =
      (match p with | .Z | .Y => SinglePauli.Z | _ => SinglePauli.I) := by
    cases p <;> rfl
  rw [hx, hz]
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [xzPhase, SinglePauli.matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.I_mul_I]

theorem cssPauli_eq_ordered_XZ (p : Fin n → SinglePauli) :
    pauliMatrix 0 p = (∏ i, xzPhase (p i)) •
      (pauliMatrix 0 (cssXWord (cssMaskX p)) * pauliMatrix 0 (cssZWord (cssMaskZ p))) := by
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul, ← tensorEntries_smul]
  congr 1
  funext i
  have h := single_eq_CSSXZ (p i)
  cases hp : p i <;> simpa [cssMaskX, cssMaskZ, cssXWord, cssZWord, hp] using h

variable (H J : Submodule CSSBit (CSSWord n)) (hHJ : H ≤ cssOrthogonal J)

theorem cssSmallPauli_detected_of_low_dual_in_checks
    (hX : ∀ w ∈ cssOrthogonal J, CSSCheckSpaces.wordWeight w < d → w ∈ H)
    (hZ : ∀ w ∈ cssOrthogonal H, CSSCheckSpaces.wordWeight w < d → w ∈ J)
    (p : Fin n → SinglePauli) (hp : (pauliSupport p).card < d) :
    GaugeOnly (physicalCSSCode H J hHJ) (pauliMatrix 0 p) := by
  classical
  let C := physicalCSSCode H J hHJ
  change GaugeOnly C _
  by_cases hx : cssMaskX p ∈ cssOrthogonal J
  · by_cases hz : cssMaskZ p ∈ cssOrthogonal H
    · have hxH := hX _ hx ((cssMaskX_weight_le p).trans_lt hp)
      have hzJ := hZ _ hz ((cssMaskZ_weight_le p).trans_lt hp)
      rw [cssPauli_eq_ordered_XZ]
      apply (gaugeOnlyComplexSubmodule C).smul_mem
      change GaugeOnly C _
      refine ⟨1,?_⟩
      change (cssEncoding H J).conjTranspose *
        (pauliMatrix 0 (cssXWord (cssMaskX p)) * pauliMatrix 0 (cssZWord (cssMaskZ p))) *
          cssEncoding H J = _
      simp only [Matrix.mul_assoc, cssEncoding_zCheck_fixes H J hHJ _ hzJ,
        cssEncoding_xCheck_fixes H J hHJ _ hxH]
      rw [show (cssEncoding H J).conjTranspose * cssEncoding H J = 1 from C.isometry,
        Matrix.one_kronecker_one]
    · change ¬ ∀ a ∈ H, dotProduct (cssMaskZ p) a = 0 at hz
      push Not at hz
      obtain ⟨a,ha,hne⟩ := hz
      have hanti := cssX_commutation a p
      simp only [cssSign, ite_eq_right hne, neg_one_smul] at hanti
      exact anticommuting_fixed_operator_gaugeOnly C _ _
        (unphased_pauliMatrix_isUnitary _) (cssEncoding_xCheck_fixes H J hHJ a ha) hanti
  · change ¬ ∀ a ∈ J, dotProduct (cssMaskX p) a = 0 at hx
    push Not at hx
    obtain ⟨a,ha,hne⟩ := hx
    have hanti := cssZ_commutation a p
    simp only [cssSign, ite_eq_right hne, neg_one_smul] at hanti
    exact anticommuting_fixed_operator_gaugeOnly C _ _
      (unphased_pauliMatrix_isUnitary _) (cssEncoding_zCheck_fixes H J hHJ a ha) hanti

theorem physicalCSSCode_detectsBelow_of_low_dual_in_checks
    (hX : ∀ w ∈ cssOrthogonal J, CSSCheckSpaces.wordWeight w < d → w ∈ H)
    (hZ : ∀ w ∈ cssOrthogonal H, CSSCheckSpaces.wordWeight w < d → w ∈ J) :
    DetectsBelow (physicalCSSCode H J hHJ) d := by
  classical
  let C := physicalCSSCode H J hHJ
  intro S hS O hO
  obtain ⟨A,hA⟩ := hO
  let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin n => 2) S)) :=
    (gaugeOnlyComplexSubmodule C).comap (localEmbedLinearMap S)
  have hspan : pauliTensorSpan S ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change GaugeOnly C (localEmbed S (tensorPauli p))
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    apply cssSmallPauli_detected_of_low_dual_in_checks H J hHJ hX hZ
    have hsub : pauliSupport (extendLocalPauli S p) ⊆ S := by
      apply pauliSupport_subset_of_outside_identity
      intro i hi
      simp [extendLocalPauli, hi]
    exact (Finset.card_le_card hsub).trans_lt hS
  rw [tensorPauli_span_eq_top] at hspan
  have hAB : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
  change GaugeOnly C (localEmbed S A) at hAB
  simpa only [hA] using hAB

theorem physicalCSSCode_hasActualDistance_of_low_dual_in_checks
    (hX : ∀ w ∈ cssOrthogonal J, CSSCheckSpaces.wordWeight w < d → w ∈ H)
    (hZ : ∀ w ∈ cssOrthogonal H, CSSCheckSpaces.wordWeight w < d → w ∈ J)
    (z : CSSWord n) (hz : z ∈ cssOrthogonal H) (hzJ : z ∉ J)
    (hweight : CSSCheckSpaces.wordWeight z = d) :
    HasActualDistance (physicalCSSCode H J hHJ) d := by
  exact ⟨physicalCSSCode_detectsBelow_of_low_dual_in_checks H J hHJ hX hZ,
    pauliSupport (cssZWord z), (cssZWord_support_card z).trans hweight,
    pauliMatrix 0 (cssZWord z), pauliMatrix_supportedOn_pauliSupport _,
    cssZWord_nongauge H J hHJ z hz hzJ⟩

#print axioms cssPauli_eq_ordered_XZ
#print axioms physicalCSSCode_detectsBelow_of_low_dual_in_checks
#print axioms physicalCSSCode_hasActualDistance_of_low_dual_in_checks

end CriticalDepth.Manuscript20261114.CSSCode
