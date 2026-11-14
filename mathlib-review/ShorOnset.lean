import FaultOnsetConsequence
import ShorLowerSaturation

/-! A rectangular Shor example has linear optimal error at the earlier onset. -/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryExperimentNormalization
open scoped ENat Topology

theorem exists_shor_at_lowerOnset (d q : ℕ) (hq : 2 ≤ q) (hd : 2 * q < d) :
    let h := lowerOnset q d
    ∃ C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1,
      IsStabilizer C ∧ HasActualDistance C d ∧
      perCodeExponent C q h = 1 ∧ paperPerCodeExponent C q h = 1 ∧
      ∃ e : Experiment C q h, e.layers.length = h ∧ e.logical = 1 ∧
        (circuitInfidelity C e.layers e.law =O[𝓝[>] 0] fun p => p) ∧
        ∃ a : ℝ, 0 < a ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
          a * p ≤ circuitInfidelity C e.layers e.law p := by
  intro h
  have hh : 1 ≤ h := clog_pos_of_two_le q (d - q) hq (by omega)
  have hOne : lowerEnvelope q d h = 1 :=
    (lowerEnvelope_eq_one_iff q d h hq hd).2 le_rfl
  have hw := exists_shor_lower_saturation_paperPerCodeExponent d q h (by omega) hq hh
  obtain ⟨C, ⟨hS, hdC, hE, hW⟩, hP⟩ := hw
  have hCast : (lowerEnvelope q d h : ℕ∞) = 1 := by rw [hOne, Nat.cast_one]
  obtain ⟨e, he, hi, hO, a, ha, ha'⟩ := hW
  refine ⟨C, hS, hdC, hE.trans hCast, hP.trans hCast, e, he, hi, ?_, a, ha, ?_⟩
  · have heq : (fun p : ℝ => p ^ lowerEnvelope q d h) = fun p => p := by
      funext p
      simp only [hOne, pow_one]
    exact heq ▸ hO
  · filter_upwards [ha'] with p hp
    have hp₁ : p ^ lowerEnvelope q d h = p := by simp only [hOne, pow_one]
    exact (congrArg (a * ·) hp₁) ▸ hp

#print axioms exists_shor_at_lowerOnset

end CriticalDepth.FaultShorSaturation
