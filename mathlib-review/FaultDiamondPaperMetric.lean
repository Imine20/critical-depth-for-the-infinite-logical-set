import FaultDiamondNormalization
import FaultDiamondTraceInputs

/-! The physical gate-list exponent is the exponent of the standard half diamond distance. -/

namespace CriticalDepth.FaultChannelEffects

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultHistoryExperimentNormalization
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultHistoryNormalization
open CriticalDepth.IndependentFaultHistories
open scoped ENat

noncomputable section

theorem paperCircuitDiamond_eq_halfCBTraceNorm {n K q : ℕ} [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (L : PaperLayers (n := n) (q := q))
    (μ : Law (PaperLabel L)) (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    paperCircuitDiamond C L μ p = sInf (Set.range fun R : RecoveryChannel
        (QubitBasis n) (Fin K × Fin 1) =>
      halfCompletelyBoundedTraceNorm (recoveredHistoryChannel μ (paperEncodedBranch C L) p R)) := by
  unfold paperCircuitDiamond optimalHistoryDiamond
  congr 1
  apply congrArg Set.range
  funext R
  have hA (x : History (PaperLabel L)) :
      (paperEncodedBranch C L x).conjTranspose * paperEncodedBranch C L x = 1 := by
    rw [paperEncodedBranch_eq_native]
    exact encodedBranch_isometry C _
  have h := historyChannel_isCPTP μ (paperEncodedBranch C L) hA p hp hp₁ R
  exact halfDiamondByEffects_eq_halfCompletelyBoundedTraceNorm _ h.1 h.2

theorem stabilizer_paperPerCodeDiamondExponent_envelopes {n k d q h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstab : IsStabilizer C) (hdistance : HasActualDistance C d)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    (lowerEnvelope q d h : ℕ∞) ≤ paperPerCodeDiamondExponent C q h ∧
      paperPerCodeDiamondExponent C q h ≤ (upperEnvelope q d h : ℕ∞) := by
  rw [paperPerCodeDiamondExponent_eq_native]
  exact stabilizer_perCodeDiamondExponent_envelopes C hstab hdistance hd hq hh

#print axioms paperCircuitDiamond_eq_halfCBTraceNorm
#print axioms stabilizer_paperPerCodeDiamondExponent_envelopes

end
end CriticalDepth.FaultChannelEffects
