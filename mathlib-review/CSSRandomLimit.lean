import CSSRandomRigidity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The probability of the union of the CSS bad events tends to zero.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open Filter CriticalDepth.Manuscript20261114.CSSCode
open scoped Topology

noncomputable section

def cssRigidityBadProbabilityBound (R : ℕ) (p : BW (cssSites R)) : ℝ :=
  (cssRigidityBadCount R p : ℝ) /
    (Nat.card (CSSJointSample p (cssXDimension R) (cssZDimension R)) : ℝ)

theorem cssRigidityBadProbabilityBound_le (R : ℕ) (hR : 2 ^ 20 ≤ R)
    (p : BW (cssSites R)) (hp : wordWeight p = cssDistance R) :
    cssRigidityBadProbabilityBound R p ≤ (2 : ℝ)⁻¹ ^ (R - 2) := by
  let Z := CSSJointSample p (cssXDimension R) (cssZDimension R)
  letI : Nonempty Z := ⟨(0, 0)⟩
  have hZ : (0 : ℝ) < (Nat.card Z : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := Z))
  have hp₂ : 0 < (2 : ℝ) ^ (R - 2) := by positivity
  have hc : (cssRigidityBadCount R p : ℝ) * (2 : ℝ) ^ (R - 2) ≤ (Nat.card Z : ℝ) := by
    exact_mod_cast cssRigidityBadCount_scaled R hR p hp
  unfold cssRigidityBadProbabilityBound
  rw [inv_pow, ← one_div]
  apply (div_le_div_iff₀ hZ hp₂).mpr
  simpa only [one_mul] using hc

theorem cssRigidityBadProbabilityBound_tendsto (q : ℕ) (hq : 2 ≤ q)
    (p : (R : ℕ) → BW (cssSites R))
    (hp : ∀ᶠ t : ℕ in atTop, wordWeight (p (q ^ t)) = cssDistance (q ^ t)) :
    Tendsto (fun t : ℕ => cssRigidityBadProbabilityBound (q ^ t) (p (q ^ t))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℕ => q ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < q by omega)
  have hsub : Tendsto (fun R : ℕ => R - 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (k + 2)] with x hx
    omega
  have high : Tendsto (fun t : ℕ => (2 : ℝ)⁻¹ ^ (q ^ t - 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (hsub.comp hpow)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds high
  · exact Eventually.of_forall (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [hpow.eventually (eventually_ge_atTop (2 ^ 20)), hp] with t ht hp
    exact cssRigidityBadProbabilityBound_le (q ^ t) ht (p (q ^ t)) hp

#print axioms cssRigidityBadProbabilityBound_tendsto

end
end CriticalDepth.Manuscript20261114.CSSCheckSpaces
