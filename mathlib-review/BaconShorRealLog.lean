import CriticalDepthMathlib
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exact real-logarithm interpretation of the aspect-ratio depth bound
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Arithmetic

theorem natCeil_log_ratio_eq_clog_ceilDiv (q a b : ℕ)
    (hq : 2 ≤ q) (ha : 0 < a) (hab : a ≤ b) :
    ⌈Real.logb (q : ℝ) ((b : ℝ) / (a : ℝ))⌉₊ = Nat.clog q (ceilDiv b a) := by
  have haq : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < b := ha.trans_le hab
  have hb'' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb'
  have hbound (h : ℕ) :
      ⌈Real.logb (q : ℝ) ((b : ℝ) / (a : ℝ))⌉₊ ≤ h ↔
        Nat.clog q (ceilDiv b a) ≤ h := by
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow haq (div_pos hb'' ha'),
      Real.rpow_natCast, div_le_iff₀ ha', Nat.clog_le_iff_le_pow (by omega : 1 < q),
      ceilDiv_le_iff _ _ _ ha]
    exact_mod_cast (Iff.rfl : b ≤ q^h * a ↔ b ≤ q^h * a)
  exact le_antisymm ((hbound _).mpr le_rfl) ((hbound _).mp le_rfl)

#print axioms natCeil_log_ratio_eq_clog_ceilDiv

end CriticalDepth.FaultShorSaturation.BaconShor
