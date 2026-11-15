import SourceConsumer
import ExactGeneration
import FaultPaperSaturationWitness

/-! Concrete applications of the exact-depth theorem and the two
original gate-list saturation theorems. -/

namespace CriticalDepth.UpdateBranchConsumer

noncomputable section

open Filter Asymptotics
open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.FaultDepthArithmetic CriticalDepth.IndependentFaultHistories
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization
open CriticalDepth.FaultAverageInfidelity CriticalDepth.FaultChannelEffects
open CriticalDepth.Manuscript20261114
open CriticalDepth.Manuscript20261114.CSSCheckSpaces CriticalDepth.Manuscript20261114.CSSCode
open scoped ENat Topology

theorem fourQubit_exactDepth_eq_max :
    let V := FourQubit.encoding
    nativeExactDepth V 2 = max (nativeCriticalDepth V 2) (nativeDenseDepth V 2) :=
  nativeExactDepth_eq_max FourQubit.encoding FourQubit.encoding_isometry
    (by decide) (by decide) 2

/-- At depth two, the distance-seven, arity-two Shor witness needs two
row groups. One physical circuit has order two for each error measure. -/
theorem shor_d7_binary_depthTwo_allMetrics :
    ∃ C : Code 84 (fun _ => 2) (2 ^ 1) 1,
      IsStabilizer (k := 1) C ∧ HasActualDistance C 7 ∧
      paperPerCodeExponent C 2 2 = (2 : ℕ∞) ∧
      paperPerCodeAverageExponent C 2 2 = (2 : ℕ∞) ∧
      paperPerCodeDiamondExponent C 2 2 = (2 : ℕ∞) ∧
      ∃ e : PaperExperiment C 2 2, e.layers.length = 2 ∧ e.logical = 1 ∧
        ∀ μ : Law (PaperLabel e.layers),
          (paperCircuitInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ (2 : ℕ)) ∧
          (paperCircuitAverageInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ (2 : ℕ)) ∧
          (paperCircuitDiamond C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ (2 : ℕ)) :=
  sharpFaultSuppression_lower_paper_witness_allMetrics 7 2 2
    (by decide) (by decide) (by decide)

/-- Specializing to binary gates leaves one CSS code for every depth in
the selected interval. The cutoff parameter stays symbolic. -/
theorem binary_css_paper_witness_interval (t : ℕ) (ht : 20 ≤ t) :
    let R := 2 ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      IsStabilizer C ∧ HasActualDistance C (cssDistance R) ∧
      cssLogicalQubits H J = cssSites R - cssXDimension R - cssZDimension R ∧
      ∀ h, 1 ≤ h → h ≤ t →
        let m := upperEnvelope 2 (cssDistance R) h
        paperPerCodeExponent C 2 h = (m : ℕ∞) ∧
        paperPerCodeAverageExponent C 2 h = (m : ℕ∞) ∧
        paperPerCodeDiamondExponent C 2 h = (m : ℕ∞) ∧
        ∃ e : PaperExperiment C 2 h, ∀ μ : Law (PaperLabel e.layers),
          (paperCircuitInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
          (paperCircuitAverageInfidelity C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
          (paperCircuitDiamond C e.layers μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) :=
  sharpFaultSuppression_upper_paper_witness_allMetrics 2 t (by decide) ht

#print axioms fourQubit_exactDepth_eq_max
#print axioms shor_d7_binary_depthTwo_allMetrics
#print axioms binary_css_paper_witness_interval

end
end CriticalDepth.UpdateBranchConsumer
