import FaultDepthOne

/-!
# Attainment and asymptotic order of a finite fault exponent
-/

namespace CriticalDepth.FaultExponent

open Filter Set Asymptotics
open scoped Topology ENat

/-- A finite exponent in the definition as a supremum of natural orders is
an attained big-O order. -/
theorem isBigO_of_exponent_eq {ε : ℝ → ℝ} {m : ℕ}
    (hm : exponent ε = (m : ℕ∞)) (hm0 : 0 < m) :
    ε =O[𝓝[>] 0] fun p => p ^ m := by
  by_contra hn
  have hb : exponent ε ≤ ((m - 1 : ℕ) : ℕ∞) := by
    apply sSup_le
    rintro _ ⟨k, rfl, hk⟩
    have hkm : k ≤ m := by exact_mod_cast (exponent_ge k hk).trans_eq hm
    have hne : k ≠ m := fun he => hn (he ▸ hk)
    exact_mod_cast (show k ≤ m - 1 by omega)
  exact (not_le_of_gt (show ((m - 1 : ℕ) : ℕ∞) < (m : ℕ∞) by exact_mod_cast
    (show m - 1 < m by omega))) (hm ▸ hb)

end CriticalDepth.FaultExponent

namespace CriticalDepth.FaultNativeCeiling

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open scoped ENat

theorem perCodeExponent_eq_one_above_upperOnset {n k d q h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstab : IsStabilizer C) (hdist : HasActualDistance C d)
    (hd : 2 * q < d) (hq : 2 ≤ q) (hh : 1 ≤ h)
    (hstart : upperOnset q d ≤ h) :
    perCodeExponent C q h = 1 := by
  obtain ⟨hl, hu⟩ := stabilizer_perCodeExponent_envelopes C hstab hdist
    (by omega) hq hh
  have hUpper : upperEnvelope q d h = 1 := (upperEnvelope_eq_one_iff q d h hq hd).mpr hstart
  have hLower : 1 ≤ lowerEnvelope q d h := ceilDiv_pos (by omega) _
  rw [hUpper] at hu
  have hLower' : (1 : ℕ∞) ≤ (lowerEnvelope q d h : ℕ∞) := by exact_mod_cast hLower
  exact le_antisymm (by simpa using hu) (hLower'.trans hl)

#print axioms CriticalDepth.FaultExponent.isBigO_of_exponent_eq
#print axioms perCodeExponent_eq_one_above_upperOnset

end CriticalDepth.FaultNativeCeiling