import FaultSharpnessAllMetrics
import FaultPaperFixedCircuit

/-! Both endpoints have actual original gate-list witnesses for all three
error measures, with one circuit for every positive choice of weights. -/

namespace CriticalDepth.Manuscript20261114

open Filter Asymptotics
open CriticalDepth.Manuscript CriticalDepth.IndependentFaultHistories
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization
open CriticalDepth.FaultAverageInfidelity CriticalDepth.FaultChannelEffects
open CriticalDepth.FaultFirstBadOrder
open CriticalDepth.Manuscript20261114.CSSCheckSpaces CriticalDepth.Manuscript20261114.CSSCode
open scoped ENat Topology

noncomputable section

/-- The universal floor and ceiling hold simultaneously for the three
optimized errors on the original gate-list model. -/
theorem sharpFaultSuppression_bounds_allMetrics {n k d q h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hS : IsStabilizer C) (hD : HasActualDistance C d)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    let lo : ℕ∞ := lowerEnvelope q d h
    let hi : ℕ∞ := upperEnvelope q d h
    (lo ≤ paperPerCodeExponent C q h ∧ paperPerCodeExponent C q h ≤ hi) ∧
    (lo ≤ paperPerCodeAverageExponent C q h ∧ paperPerCodeAverageExponent C q h ≤ hi) ∧
    (lo ≤ paperPerCodeDiamondExponent C q h ∧ paperPerCodeDiamondExponent C q h ≤ hi) := by
  dsimp only
  rw [paperPerCodeAverageExponent_eq, paperPerCodeDiamondExponent_eq_entanglement]
  have hBounds := sharpFaultSuppression_bounds C hS hD hd hq hh
  exact ⟨hBounds, hBounds, hBounds⟩


/-- A depth-exact, logical-identity Shor circuit attains the lower envelope
on the original register for all three separately optimized errors. -/
theorem sharpFaultSuppression_lower_paper_witness_allMetrics (d q h : ℕ)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    let m := lowerEnvelope q d h
    ∃ C : Code (m * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      IsStabilizer C ∧ HasActualDistance C d ∧
      paperPerCodeExponent C q h = (m : ℕ∞) ∧
      paperPerCodeAverageExponent C q h = (m : ℕ∞) ∧
      paperPerCodeDiamondExponent C q h = (m : ℕ∞) ∧
      ∃ e : PaperExperiment C q h, e.layers.length = h ∧ e.logical = 1 ∧
        ∀ μ : Law (PaperLabel e.layers),
          (paperCircuitInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
          (paperCircuitAverageInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
          (paperCircuitDiamond C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) := by
  let m := lowerEnvelope q d h
  obtain ⟨C, ⟨hS, hD, _, hW⟩, hEnt, hAvg, hDia⟩ :=
    sharpFaultSuppression_lower_allMetrics d q h hd hq hh
  obtain ⟨e, he, hi, hO, a, ha, hlo⟩ := hW
  let E := paperExperimentOfNative e
  have hNative : FaultExponent.exponent (circuitInfidelity C e.layers e.law) =
      (m : ℕ∞) :=
    le_antisymm (FaultExponent.exponent_le_of_powerLower ha m hlo)
      (FaultExponent.exponent_ge m hO)
  have hPaper : FaultExponent.exponent (paperCircuitInfidelity C E.layers E.law) =
      (m : ℕ∞) := by
    change FaultExponent.exponent
      (paperCircuitInfidelity C (paperLayersOfNative e.layers) (reverseLaw e.layers e.law)) = _
    rw [← nativeCircuitInfidelity_eq_paper]
    exact hNative
  refine ⟨C, hS, hD, hEnt, hAvg, hDia, E, ?_, hi, ?_⟩
  · simpa only [E, paperExperimentOfNative, paperLayersOfNative, List.length_map] using he
  · intro μ
    exact paperCircuitErrors_isTheta_of_exponent_eq_any_law C E.layers E.law μ m hPaper

/-- One physical CSS code works throughout the stipulated depth interval.
At each depth an actual gate list witnesses the upper envelope simultaneously
for all three optimized errors, independently of the positive weights. -/
theorem sharpFaultSuppression_upper_paper_witness_allMetrics
    (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      IsStabilizer C ∧ HasActualDistance C (cssDistance R) ∧
      cssLogicalQubits H J = cssSites R - cssXDimension R - cssZDimension R ∧
      ∀ h, 1 ≤ h → h ≤ t →
        let m := upperEnvelope q (cssDistance R) h
        paperPerCodeExponent C q h = (m : ℕ∞) ∧
        paperPerCodeAverageExponent C q h = (m : ℕ∞) ∧
        paperPerCodeDiamondExponent C q h = (m : ℕ∞) ∧
        ∃ e : PaperExperiment C q h, ∀ μ : Law (PaperLabel e.layers),
          (paperCircuitInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
          (paperCircuitAverageInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
          (paperCircuitDiamond C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) := by
  let R := q ^ t
  obtain ⟨H, J, hc, hS, hD, hDim, hSat⟩ := sharpFaultSuppression_upper_allMetrics q t hq ht
  let C := physicalCSSCode H J hc
  refine ⟨H, J, hc, hS, hD, hDim, ?_⟩
  intro h hh hht
  let m := upperEnvelope q (cssDistance R) h
  obtain ⟨hEnt, hAvg, hDia⟩ := hSat h hh hht
  obtain ⟨e, he⟩ := exists_paperExperiment_at_finite_perCodeExponent C q h m hEnt
  exact ⟨hEnt, hAvg, hDia, e, fun μ =>
    paperCircuitErrors_isTheta_of_exponent_eq_any_law C e.layers e.law μ m he⟩

#print axioms sharpFaultSuppression_bounds_allMetrics
#print axioms sharpFaultSuppression_lower_paper_witness_allMetrics
#print axioms sharpFaultSuppression_upper_paper_witness_allMetrics

end
end CriticalDepth.Manuscript20261114
