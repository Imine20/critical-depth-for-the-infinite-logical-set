import FaultHaarShor
import CSSUpperSaturationFamily

/-!
The CSS upper-envelope family attains the same exponent for the Haar
average over logical input states.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultDepthArithmetic
open CriticalDepth.Manuscript20261114.CSSCheckSpaces
open CriticalDepth.Manuscript20261114.CSSCode
open scoped ENat

theorem exists_css_upper_saturation_average (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      IsStabilizer C ∧ HasActualDistance C (cssDistance R) ∧
      cssLogicalQubits H J = cssSites R - cssXDimension R - cssZDimension R ∧
      ∀ h, 1 ≤ h → h ≤ t →
        perCodeAverageExponent C q h = (upperEnvelope q (cssDistance R) h : ℕ∞) ∧
        paperPerCodeAverageExponent C q h = (upperEnvelope q (cssDistance R) h : ℕ∞) := by
  obtain ⟨H, J, hc, hS, hD, hdim, hs⟩ := exists_css_upper_saturation q t hq ht
  refine ⟨H, J, hc, hS, hD, hdim, ?_⟩
  intro h hh hht
  exact ⟨(perCodeAverageExponent_eq _ _ _).trans (hs h hh hht).1,
    (paperPerCodeAverageExponent_eq _ _ _).trans (hs h hh hht).2⟩

#print axioms exists_css_upper_saturation_average

end
end CriticalDepth.FaultAverageInfidelity
