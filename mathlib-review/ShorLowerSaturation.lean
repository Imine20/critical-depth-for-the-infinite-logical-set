import ShorMultilayerSaturation
import ShorDepthOneWitness
import FaultHistoryExperimentNormalization

/-!
# Sharpness of the lower envelope for all positive depths

This is the manuscript's rectangular family on exactly N d physical
qubits, with N = ceil(d/(q^h+q)) (q^h+q).
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryExperimentNormalization CriticalDepth.ShorDepthOneWitness
open scoped ENat Topology

def shorLowerSaturationWitness {n : ℕ}
    (C : Code n (fun _ => 2) (2 ^ 1) 1) (q d h : ℕ) : Prop :=
  IsStabilizer C ∧ HasActualDistance C d ∧
  perCodeExponent C q h = (lowerEnvelope q d h : ℕ∞) ∧
  ∃ e : Experiment C q h, e.layers.length = h ∧ e.logical = 1 ∧
    (circuitInfidelity C e.layers e.law =O[𝓝[>] 0] fun p => p ^ lowerEnvelope q d h) ∧
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
      a * p ^ lowerEnvelope q d h ≤ circuitInfidelity C e.layers e.law p

theorem exists_shor_lower_saturation (d q h : ℕ)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      shorLowerSaturationWitness C q d h := by
  by_cases h₁ : h = 1
  · subst h
    exact exists_depth_one_actual_lower_saturation d q hd hq
  · exact exists_multilayer_lower_saturation d q h hd hq (by omega)

theorem exists_shor_lower_saturation_paperPerCodeExponent (d q h : ℕ)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      shorLowerSaturationWitness C q d h ∧
      paperPerCodeExponent C q h = (lowerEnvelope q d h : ℕ∞) := by
  obtain ⟨C, hC⟩ := exists_shor_lower_saturation d q h hd hq hh
  exact ⟨C, hC, (paperPerCodeExponent_eq_native C q h).trans hC.2.2.1⟩

#print exists_shor_lower_saturation
#print axioms exists_shor_lower_saturation
#print axioms exists_shor_lower_saturation_paperPerCodeExponent

end CriticalDepth.FaultShorSaturation