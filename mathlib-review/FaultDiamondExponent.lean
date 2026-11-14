import FaultDiamondTail
import FaultSupportPreserving
import FaultOnsetConsequence
import ShorLowerSaturation

/-!
The fault exponent bounds and both saturations with terminal recovery
optimized for the half diamond distance.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix Filter Asymptotics
open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultSupportPreserving CriticalDepth.FaultNativeCeiling
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open scoped BigOperators ENat Topology Kronecker

noncomputable section

theorem exponent_le_of_eventualLoss_dominance {f g : ℝ → ℝ}
    (h : ∀ᶠ p in 𝓝[>] (0 : ℝ), 0 ≤ f p ∧ f p ≤ g p) :
    FaultExponent.exponent g ≤ FaultExponent.exponent f := by
  apply sSup_le
  rintro _ ⟨m, rfl, hm⟩
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hm
  apply FaultExponent.exponent_ge
  refine Asymptotics.isBigO_iff.mpr ⟨c, ?_⟩
  filter_upwards [h, hc] with p hp he
  have hg : 0 ≤ g p := hp.1.trans hp.2
  rw [Real.norm_eq_abs, abs_of_nonneg hg] at he
  rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
  exact hp.2.trans he

variable {n K q h : ℕ}

def circuitDiamond (C : Code n (fun _ => 2) K 1) (L : Layers n q)
    (μ : Law (fun i : Location L => FaultLabel i)) [Nonempty (Fin K × Fin 1)] : ℝ → ℝ :=
  optimalHistoryDiamond μ (encodedBranch C)

def perCodeDiamondExponent (C : Code n (fun _ => 2) K 1) (q h : ℕ)
    [Nonempty (Fin K × Fin 1)] : ℕ∞ :=
  FaultExponent.worstCaseExponent fun e : Experiment C q h =>
    circuitDiamond C e.layers e.law

theorem perCodeDiamondExponent_le_infidelity (C : Code n (fun _ => 2) K 1) (q h : ℕ)
    [Nonempty (Fin K × Fin 1)] :
    perCodeDiamondExponent C q h ≤ perCodeExponent C q h := by
  apply le_iInf
  intro e
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, by norm_num, subset_rfl⟩
  apply (iInf_le _ e).trans
  apply exponent_le_of_eventualLoss_dominance
  filter_upwards [hIoo] with p hp
  refine ⟨?_, optimalInfidelity_le_optimalHistoryDiamond e.law (encodedBranch C)
    (encodedBranch_isometry C) p hp.1.le hp.2.le⟩
  exact FaultExponent.optimalLoss_nonneg e.law _ (fun x T =>
    (branchLoss_mem_Icc (encodedBranch C x) (encodedBranch_isometry C x) T).1) hp.1.le hp.2.le

theorem native_circuitDiamond_floor [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (d : ℕ) (hdetect : DetectsBelow C d)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i))
    (hq : 1 ≤ q) (W : Operator (Fin K)) (hW : Implements C (layerSequenceEval L) W) :
    (lowerEnvelope q d L.length : ℕ∞) ≤ FaultExponent.exponent (circuitDiamond C L μ) := by
  obtain ⟨hW, Z, hZ, hV⟩ := hW
  have hdual : C.encoding.conjTranspose * layerSequenceEval L =
      (W ⊗ₖ Z) * C.encoding.conjTranspose := by
    have heval := circuitOfLayers_eval L
    rw [← heval] at hV ⊢
    exact point_encoded_dual C (circuitOfLayers L) W Z hW hZ hV
  apply guaranteed_historyDiamond_exponent μ (encodedBranch C) (encodedBranch_isometry C)
  intro x y hx hy
  exact histories_scalarCrossTerm (insertion L) physicalFault physicalFault_supported x y
    chronologicalFaults mem_chronologicalFaults hq d _ (le_max_left _ _) (le_max_right _ _)
    (max_lt hx hy) C hdetect W Z hW hZ hV hdual

theorem perCodeDiamondExponent_floor [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (q d h : ℕ) (hq : 1 ≤ q) (hdetect : DetectsBelow C d) :
    (lowerEnvelope q d h : ℕ∞) ≤ perCodeDiamondExponent C q h := by
  apply le_iInf
  intro e
  apply le_trans _ (native_circuitDiamond_floor C d hdetect e.layers e.law hq e.logical e.exactAction)
  have hden : q ^ e.layers.length + q ≤ q ^ h + q :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) e.depth) _
  have hpos : 0 < q ^ h + q := by omega
  have hpos' : 0 < q ^ e.layers.length + q := by omega
  have hceil := (ceilDiv_le_iff d _ (lowerEnvelope q d e.layers.length) hpos').mp le_rfl
  exact_mod_cast (ceilDiv_le_iff d _ (lowerEnvelope q d e.layers.length) hpos).mpr
    (hceil.trans (Nat.mul_le_mul_left _ hden))

theorem stabilizer_perCodeDiamondExponent_envelopes {k d h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstabilizer : IsStabilizer C)
    (hdistance : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    (lowerEnvelope q d h : ℕ∞) ≤ perCodeDiamondExponent C q h ∧
      perCodeDiamondExponent C q h ≤ (upperEnvelope q d h : ℕ∞) :=
  ⟨perCodeDiamondExponent_floor C q d h (by omega) hdistance.1,
    (perCodeDiamondExponent_le_infidelity C q h).trans
      (perCodeExponent_ceiling C hstabilizer hdistance hd hq hh)⟩

theorem exists_shor_diamond_lower_saturation (d q h : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      IsStabilizer C ∧ HasActualDistance C d ∧
      perCodeDiamondExponent C q h = (lowerEnvelope q d h : ℕ∞) := by
  obtain ⟨C, hstab, hdist, hExp, _⟩ := FaultShorSaturation.exists_shor_lower_saturation d q h hd hq hh
  exact ⟨C, hstab, hdist, le_antisymm ((perCodeDiamondExponent_le_infidelity C q h).trans_eq hExp)
    (perCodeDiamondExponent_floor C q d h (by omega) hdist.1)⟩

theorem perCodeDiamondExponent_eq_upper_of_preservesSupports {k d h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstab : IsStabilizer C)
    (hdist : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h)
    (hrigidity : ∀ e : Experiment C q h, PreservesSupports (layerSequenceEval e.layers)) :
    perCodeDiamondExponent C q h = (upperEnvelope q d h : ℕ∞) := by
  apply le_antisymm ((perCodeDiamondExponent_le_infidelity C q h).trans
    (perCodeExponent_ceiling C hstab hdist hd hq hh))
  apply le_iInf
  intro e
  exact guaranteed_historyDiamond_exponent e.law (encodedBranch C) (encodedBranch_isometry C)
    (upperEnvelope q d h) (scalarCrossTerms_of_preservesSupports C d h (by omega)
      hdist.1 e.depth (hrigidity e))

/-- The actual worst circuit in the lower-saturating Shor example has the same
leading order for half diamond distance. -/
theorem shorWitness_diamondTheta {d q h n : ℕ}
    (C : Code n (fun _ => 2) (2 ^ 1) 1) (hC : FaultShorSaturation.shorLowerSaturationWitness C q d h)
    (hd : 2 ≤ d) (hq : 2 ≤ q) :
    ∃ e : Experiment C q h, e.layers.length = h ∧ e.logical = 1 ∧
      (circuitDiamond C e.layers e.law =O[𝓝[>] 0] fun p => p ^ lowerEnvelope q d h) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
        a * p ^ lowerEnvelope q d h ≤ circuitDiamond C e.layers e.law p := by
  obtain ⟨_, hdist, _, e, he, hI, _, a, ha, hLower⟩ := hC
  have hFloor := native_circuitDiamond_floor C d hdist.1 e.layers e.law (by omega)
    e.logical e.exactAction
  have hFloor' : (lowerEnvelope q d h : ℕ∞) ≤
      FaultExponent.exponent (circuitDiamond C e.layers e.law) := by
    exact (congrArg (fun j => (lowerEnvelope q d j : ℕ∞)) he) ▸ hFloor
  have hsmall : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, by norm_num, subset_rfl⟩
  have hCompare : ∀ᶠ p in 𝓝[>] (0 : ℝ),
      a * p ^ lowerEnvelope q d h ≤ circuitDiamond C e.layers e.law p := by
    filter_upwards [hLower, hsmall] with p hp hp'
    exact hp.trans (optimalInfidelity_le_optimalHistoryDiamond e.law (encodedBranch C)
      (encodedBranch_isometry C) p hp'.1.le hp'.2.le)
  have hLowerExp := FaultExponent.exponent_le_of_powerLower ha (lowerEnvelope q d h) hCompare
  have hPos : 0 < lowerEnvelope q d h := ceilDiv_pos (by omega) _
  exact ⟨e, he, hI, FaultExponent.isBigO_of_exponent_eq (le_antisymm hLowerExp hFloor') hPos,
    a, ha, hCompare⟩

#print axioms shorWitness_diamondTheta
#print axioms stabilizer_perCodeDiamondExponent_envelopes
#print axioms exists_shor_diamond_lower_saturation
#print axioms perCodeDiamondExponent_eq_upper_of_preservesSupports

end
end CriticalDepth.FaultChannelEffects