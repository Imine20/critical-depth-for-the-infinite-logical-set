import FaultDiamondExponent
import FaultChannelNormalization

/-!
The diamond optimization is invariant under padding and normalizing native gate lists.
-/

namespace CriticalDepth.FaultChannelEffects

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultCPTPRepresentation
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization
open CriticalDepth.FaultDepthArithmetic
open scoped ENat BigOperators

noncomputable section

variable {n K q : ℕ} [Nonempty (Fin K × Fin 1)]

def paperCircuitDiamond (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) : ℝ → ℝ :=
  optimalHistoryDiamond μ (paperEncodedBranch C L)

theorem paperCircuitDiamond_eq_native (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) :
    paperCircuitDiamond C L μ = circuitDiamond C (normalizedLayers L) (pushLaw L μ) := by
  funext p
  unfold paperCircuitDiamond circuitDiamond optimalHistoryDiamond
  apply congrArg (sInf : Set ℝ → ℝ)
  apply congrArg Set.range
  funext R
  apply congrArg halfDiamondByEffects
  exact paperRecoveredHistoryChannel_eq_native C L μ p R

theorem nativeCircuitDiamond_eq_paper (C : Code n (fun _ => 2) K 1)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i)) :
    circuitDiamond C L μ = paperCircuitDiamond C (paperLayersOfNative L) (reverseLaw L μ) := by
  funext p
  unfold paperCircuitDiamond circuitDiamond optimalHistoryDiamond
  apply congrArg (sInf : Set ℝ → ℝ)
  apply congrArg Set.range
  funext R
  apply congrArg halfDiamondByEffects
  exact nativeRecoveredHistoryChannel_eq_paper C L μ p R

def paperPerCodeDiamondExponent (C : Code n (fun _ => 2) K 1) (q h : ℕ) : ℕ∞ :=
  FaultExponent.worstCaseExponent fun e : PaperExperiment C q h =>
    paperCircuitDiamond C e.layers e.law

theorem paperPerCodeDiamondExponent_eq_native (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    paperPerCodeDiamondExponent C q h = perCodeDiamondExponent C q h := by
  apply le_antisymm
  · apply le_iInf
    intro e
    change paperPerCodeDiamondExponent C q h ≤ FaultExponent.exponent (circuitDiamond C e.layers e.law)
    rw [nativeCircuitDiamond_eq_paper]
    exact iInf_le (fun t : PaperExperiment C q h => FaultExponent.exponent
      (paperCircuitDiamond C t.layers t.law)) (paperExperimentOfNative e)
  · apply le_iInf
    intro e
    change perCodeDiamondExponent C q h ≤ FaultExponent.exponent (paperCircuitDiamond C e.layers e.law)
    rw [paperCircuitDiamond_eq_native]
    exact iInf_le (fun t : Experiment C q h => FaultExponent.exponent
      (circuitDiamond C t.layers t.law)) (normalizeExperiment e)

#print axioms paperPerCodeDiamondExponent_eq_native

end
end CriticalDepth.FaultChannelEffects
