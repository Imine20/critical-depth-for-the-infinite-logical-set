import FaultDiamondExponent
import CSSUpperSaturationFamily

/-! The CSS saturation applies to the same physical code and both optimized metrics. -/

namespace CriticalDepth.FaultChannelEffects

open CriticalDepth.Manuscript CriticalDepth.FaultDepthArithmetic
open CriticalDepth.FaultNativeModel
open CriticalDepth.Manuscript20261114.CSSCode CriticalDepth.Manuscript20261114.CSSCheckSpaces
open scoped ENat Matrix

noncomputable section

/-- The same physical CSS code attains both exponent ceilings on the whole interval. -/
theorem exists_css_diamond_upper_saturation (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      IsStabilizer C ∧ HasActualDistance C (cssDistance R) ∧
      cssLogicalQubits H J = cssSites R - cssXDimension R - cssZDimension R ∧
      ∀ h, 1 ≤ h → h ≤ t →
        perCodeDiamondExponent C q h = (upperEnvelope q (cssDistance R) h : ℕ∞) ∧
        perCodeExponent C q h = (upperEnvelope q (cssDistance R) h : ℕ∞) := by
  let R := q ^ t
  have hR : 2 ^ 20 ≤ R := (Nat.pow_le_pow_right (by decide) ht).trans (Nat.pow_le_pow_left hq t)
  obtain ⟨H, J, p, S, hH, hJ, hp, hpd, hDual⟩ := exists_rigid_checkSpaces R hR
  obtain ⟨B, hRows, hB⟩ := exists_css_check_matrix J
  have hd : 2 ≤ cssDistance R := by
    have hR2 : 2 ≤ R := (by decide : 2 ≤ 2 ^ 20).trans hR
    unfold cssDistance
    nlinarith
  have hp₀ : p ≠ 0 := by
    rintro rfl
    simp [wordWeight] at hpd
    omega
  have hpJ : p ∉ J := by
    intro h
    have hDist := S.zDistance p h hp₀
    rw [hH, hJ, hpd] at hDist
    exact (not_lt_of_ge (cssDistance_le_deletionThreshold R (by omega))) hDist
  have hdR : cssDistance R ≤ q ^ t * (Module.finrank CSSBit H + 1) := by
    rw [hH]
    exact cssDistance_le_supportBound R (by omega)
  have hs := physicalCSSCode_isStabilizer H J S.compatible
  have h := physicalCSS_attains_upperEnvelope hq hd H J S p hp hpJ hpd hDual hdR B hRows hB
  refine ⟨H, J, S.compatible, hs, h.1, ?_, ?_⟩
  · rw [cssLogicalQubits_eq_sub H J S.compatible, hH, hJ]
  · intro l hl hlt
    refine ⟨?_, h.2 l hl hlt⟩
    apply perCodeDiamondExponent_eq_upper_of_preservesSupports _ hs h.1 hd hq hl
    intro e
    have hRpos : 1 ≤ R := (by decide : 1 ≤ 2 ^ 20).trans hR
    exact physicalCSS_exactCircuit_preservesSupports H J q R (by omega)
      hRpos S B hRows hB e.layers
      (Nat.pow_le_pow_right (by omega) (e.depth.trans hlt)) e.logical e.exactAction

#print axioms exists_css_diamond_upper_saturation

end
end CriticalDepth.FaultChannelEffects
