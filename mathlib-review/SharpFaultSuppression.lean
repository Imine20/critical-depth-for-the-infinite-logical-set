import CSSUpperGap
import ShorLowerSaturation
import MidpointLogicalCeiling

/-! Sharpness of both fault-suppression envelopes on the original registers. -/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryExperimentNormalization CriticalDepth.FaultNativeCeiling
open CriticalDepth.Manuscript20261114.CSSCode CriticalDepth.Manuscript20261114.CSSCheckSpaces
open scoped ENat

theorem sharpFaultSuppression_bounds {n k d q h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hS : IsStabilizer C) (hD : HasActualDistance C d)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    (lowerEnvelope q d h : ℕ∞) ≤ paperPerCodeExponent C q h ∧
      paperPerCodeExponent C q h ≤ (upperEnvelope q d h : ℕ∞) := by
  rw [paperPerCodeExponent_eq_native]
  exact ⟨perCodeExponent_floor C q d h (by omega) hD.1,
    perCodeExponent_ceiling_of_logicalPauli C hS hD hd hq hh⟩

theorem sharpFaultSuppression_lower (d q h : ℕ)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      IsStabilizer C ∧ HasActualDistance C d ∧
      paperPerCodeExponent C q h = (lowerEnvelope q d h : ℕ∞) := by
  obtain ⟨C, hC, hE⟩ := exists_shor_lower_saturation_paperPerCodeExponent d q h hd hq hh
  exact ⟨C, hC.1, hC.2.1, hE⟩

theorem sharpFaultSuppression_upper (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (R ^ 12))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      IsStabilizer C ∧ HasActualDistance C (q ^ (2 * t)) ∧
      cssLogicalQubits H J = R ^ 12 - R ^ 4 - R ^ 6 ∧
      ∀ h, 1 ≤ h → h ≤ t →
        paperPerCodeExponent C q h = (upperEnvelope q (q ^ (2 * t)) h : ℕ∞) := by
  intro R
  have he : cssDistance R = q ^ (2 * t) := by
    change (q ^ t) ^ 2 = _
    rw [← pow_mul, mul_comm]
  obtain ⟨H, J, hc, hS, hD, hK, hExp⟩ := exists_css_upper_saturation q t hq ht
  refine ⟨H, J, hc, hS, ?_, hK, ?_⟩
  · exact he ▸ hD
  · intro h hh hht
    exact he ▸ (hExp h hh hht).2

#print axioms sharpFaultSuppression_bounds
#print axioms sharpFaultSuppression_lower
#print axioms sharpFaultSuppression_upper

end CriticalDepth.Manuscript20261114
