import CSSUpperSaturationFamily
import FaultEnvelopeScaling

/-!
The growing-depth separation of the attained CSS exponent from the lower envelope.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode CriticalDepth.FaultNativeModel
open CriticalDepth.FaultDepthArithmetic
open scoped ENat

theorem exists_css_code_with_strict_exponent_gap (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      (lowerEnvelope q (cssDistance R) t : ℕ∞) < perCodeExponent C q t := by
  obtain ⟨H, J, hc, _, _, _, h⟩ := exists_css_upper_saturation q t hq ht
  refine ⟨H, J, hc, ?_⟩
  change (lowerEnvelope q (cssDistance (q ^ t)) t : ℕ∞) <
    perCodeExponent (physicalCSSCode H J hc) q t
  rw [(h t (by omega) le_rfl).1]
  have hpow : cssDistance (q ^ t) = q ^ (2 * t) := by
    rw [cssDistance, ← pow_mul, mul_comm]
  rw [hpow]
  exact_mod_cast envelopes_midpoint_strict q t hq (by omega)


/-- One physical code simultaneously realizes the upper-envelope scaling
and has a square-root universal lower envelope at the midpoint depth. -/
theorem exists_css_code_with_midpoint_scaling (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    let d := cssDistance R
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let m : ℕ := upperEnvelope q d t
      perCodeExponent (physicalCSSCode H J hc) q t = (m : ℕ∞) ∧
      ((d : ℝ) ^ (3 / 4 : ℝ) / (2 * q) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ 2 * (d : ℝ) ^ (3 / 4 : ℝ)) ∧
      (Real.sqrt (d : ℝ) / 2 ≤ (lowerEnvelope q d t : ℝ) ∧
        (lowerEnvelope q d t : ℝ) ≤ Real.sqrt (d : ℝ)) := by
  obtain ⟨H, J, hc, _, _, _, h⟩ := exists_css_upper_saturation q t hq ht
  refine ⟨H, J, hc, (h t (by omega) le_rfl).1, ?_⟩
  have hd : cssDistance (q ^ t) = q ^ (2 * t) := by
    rw [cssDistance, ← pow_mul, mul_comm]
  rw [hd]
  refine ⟨?_, ?_⟩
  · simpa only [Nat.cast_pow] using upperEnvelope_midpoint_threeQuarterBounds q t hq
  · simpa only [Nat.cast_pow] using
      lowerEnvelope_midpoint_squareRootBounds q t (by omega) (by omega)

#print axioms exists_css_code_with_midpoint_scaling
#print axioms exists_css_code_with_strict_exponent_gap

end CriticalDepth.Manuscript20261114.CSSCheckSpaces