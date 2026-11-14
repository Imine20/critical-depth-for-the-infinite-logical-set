import FaultHaarNativeModel
import ShorLowerSaturation

/-!
The Shor lower-envelope experiment also attains the same asymptotic order
for the Haar average over logical input states.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultShorSaturation
open Asymptotics Filter
open scoped ENat Topology

theorem exists_shor_lower_saturation_average (d q h : ℕ)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      shorLowerSaturationWitness C q d h ∧
      paperPerCodeAverageExponent C q h = (lowerEnvelope q d h : ℕ∞) ∧
      ∃ e : Experiment C q h, e.layers.length = h ∧ e.logical = 1 ∧
        (circuitAverageInfidelity C e.layers e.law =O[𝓝[>] 0] fun p => p ^ lowerEnvelope q d h) ∧
        ∃ a : ℝ, 0 < a ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
          a * p ^ lowerEnvelope q d h ≤ circuitAverageInfidelity C e.layers e.law p := by
  obtain ⟨C, hC, hp⟩ := exists_shor_lower_saturation_paperPerCodeExponent d q h hd hq hh
  refine ⟨C, hC, (paperPerCodeAverageExponent_eq C q h).trans hp, ?_⟩
  obtain ⟨e, hd', he, hO, a, ha, hlow⟩ := hC.2.2.2
  let c := fidelityDimensionRatio (Fin (2 ^ 1) × Fin 1)
  have hc : 0 < c := fidelityDimensionRatio_pos _
  have heq : circuitAverageInfidelity C e.layers e.law =
      fun p => c * circuitInfidelity C e.layers e.law p :=
    funext (circuitAverageInfidelity_eq_dim_ratio C e.layers e.law)
  refine ⟨e, hd', he, ?_, c * a, mul_pos hc ha, ?_⟩
  · rw [heq]
    exact hO.const_mul_left c
  · filter_upwards [hlow] with p hp
    rw [heq, mul_assoc]
    exact mul_le_mul_of_nonneg_left hp hc.le

#print axioms exists_shor_lower_saturation_average

end
end CriticalDepth.FaultAverageInfidelity
