import SharpFaultSuppression
import FaultHaarNativeModel
import FaultDiamondPaperMetric
import FaultDiamondCSSSaturation

/-! Simultaneous saturation for the three optimized error measures on the same code. -/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel CriticalDepth.FaultDepthArithmetic
open CriticalDepth.FaultShorSaturation CriticalDepth.FaultHistoryExperimentNormalization
open CriticalDepth.FaultChannelEffects CriticalDepth.FaultAverageInfidelity
open CriticalDepth.Manuscript20261114.CSSCheckSpaces CriticalDepth.Manuscript20261114.CSSCode
open scoped ENat

theorem sharpFaultSuppression_lower_allMetrics (d q h : ℕ)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    let m : ℕ∞ := lowerEnvelope q d h
    ∃ C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      shorLowerSaturationWitness C q d h ∧
      paperPerCodeExponent C q h = m ∧ paperPerCodeAverageExponent C q h = m ∧
      paperPerCodeDiamondExponent C q h = m := by
  obtain ⟨C, hC, hE⟩ := exists_shor_lower_saturation_paperPerCodeExponent d q h hd hq hh
  refine ⟨C, hC, hE, (paperPerCodeAverageExponent_eq C q h).trans hE, ?_⟩
  rw [paperPerCodeDiamondExponent_eq_native]
  apply le_antisymm
  · exact (perCodeDiamondExponent_le_infidelity C q h).trans_eq
      ((paperPerCodeExponent_eq_native C q h).symm.trans hE)
  · exact perCodeDiamondExponent_floor C q d h (by omega) hC.2.1.1

theorem sharpFaultSuppression_upper_allMetrics (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      IsStabilizer C ∧ HasActualDistance C (cssDistance R) ∧
      cssLogicalQubits H J = cssSites R - cssXDimension R - cssZDimension R ∧
      ∀ h, 1 ≤ h → h ≤ t →
        let m : ℕ∞ := upperEnvelope q (cssDistance R) h
        paperPerCodeExponent C q h = m ∧ paperPerCodeAverageExponent C q h = m ∧
        paperPerCodeDiamondExponent C q h = m := by
  obtain ⟨H, J, hc, hS, hD, hDim, hSat⟩ := exists_css_diamond_upper_saturation q t hq ht
  refine ⟨H, J, hc, hS, hD, hDim, ?_⟩
  intro h hh hht
  obtain ⟨hDiamond, hEnt⟩ := hSat h hh hht
  have hPaper := (paperPerCodeExponent_eq_native _ q h).trans hEnt
  exact ⟨hPaper, (paperPerCodeAverageExponent_eq _ q h).trans hPaper,
    (paperPerCodeDiamondExponent_eq_native _ q h).trans hDiamond⟩

#print axioms sharpFaultSuppression_lower_allMetrics
#print axioms sharpFaultSuppression_upper_allMetrics

end CriticalDepth.Manuscript20261114