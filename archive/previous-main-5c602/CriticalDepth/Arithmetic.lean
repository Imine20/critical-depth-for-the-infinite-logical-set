import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Arithmetic dependencies for the critical-depth manuscript

The source manuscript is bound separately by its SHA-256 manifest. This module
proves only integer threshold, light-cone, and support-count arithmetic. It does
not define quantum codes or circuits and does not prove either main theorem.

For positive arity, `ceilDiv w q` is the usual ceiling of `w / q`. The explicit
zero case makes the iteration meaningful for an empty support as well.
-/

namespace CriticalDepth.Arithmetic

def ceilHalf (h : ℕ) : ℕ := (h + 1) / 2

def criticalDepth (q d : ℕ) : ℕ := 2 * Nat.clog q d - 1

/-- Bridge from the discrete ceiling logarithm to the manuscript's real formula. -/
theorem clog_eq_natCeil_log (q d : ℕ) :
    Nat.clog q d = ⌈Real.log (d : ℝ) / Real.log (q : ℝ)⌉₊ := by
  simpa only [Real.logb] using (Real.natCeil_logb_natCast q d).symm

theorem criticalDepth_eq_log (q d : ℕ) :
    criticalDepth q d = 2 * ⌈Real.log (d : ℝ) / Real.log (q : ℝ)⌉₊ - 1 := by
  unfold criticalDepth
  rw [clog_eq_natCeil_log]

/-- The strict depth threshold is exactly the strict two-sided cone bound. -/
theorem below_threshold_iff (q d h : ℕ) (hq : 2 ≤ q) :
    h < criticalDepth q d ↔ q ^ ceilHalf h < d := by
  have hq' : 1 < q := by omega
  change h < 2 * Nat.clog q d - 1 ↔ q ^ ((h + 1) / 2) < d
  rw [← Nat.lt_clog_iff_pow_lt hq']
  omega

theorem below_threshold_log_iff (q d h : ℕ) (hq : 2 ≤ q) :
    h < 2 * ⌈Real.log (d : ℝ) / Real.log (q : ℝ)⌉₊ - 1 ↔
      q ^ ceilHalf h < d := by
  rw [← criticalDepth_eq_log]
  exact below_threshold_iff q d h hq

/-- Unary gates satisfy the cone inequality at every finite depth, without `log₁`. -/
theorem unary_cone_bound (d h : ℕ) (hd : 2 ≤ d) :
    (1 : ℕ) ^ ceilHalf h < d := by
  simpa only [one_pow] using (show 1 < d by omega)

/-- One of the forward and backward layer counts is at most `ceil(h/2)`. -/
theorem layer_min_le_ceilHalf (h ℓ : ℕ) (_hℓ : 1 ≤ ℓ) (hℓh : ℓ ≤ h) :
    min ℓ (h - ℓ + 1) ≤ ceilHalf h := by
  unfold ceilHalf
  by_cases ha : ℓ ≤ (h + 1) / 2
  · exact (min_le_left _ _).trans ha
  · have hb : h - ℓ + 1 ≤ (h + 1) / 2 := by omega
    exact (min_le_right _ _).trans hb

def ceilDiv (w q : ℕ) : ℕ := if w = 0 then 0 else (w - 1) / q + 1

@[simp] theorem ceilDiv_zero (q : ℕ) : ceilDiv 0 q = 0 := by
  simp [ceilDiv]

@[simp] theorem ceilDiv_one (w : ℕ) : ceilDiv w 1 = w := by
  cases w <;> simp [ceilDiv]

theorem ceilDiv_of_pos {w : ℕ} (hw : 0 < w) (q : ℕ) :
    ceilDiv w q = (w - 1) / q + 1 := by
  simp [ceilDiv, Nat.ne_of_gt hw]

theorem ceilDiv_pos {w : ℕ} (hw : 0 < w) (q : ℕ) : 0 < ceilDiv w q := by
  rw [ceilDiv_of_pos hw]
  exact Nat.succ_pos _

/-- Ceiling divisions compose by multiplying their denominators. -/
theorem ceilDiv_comp (w a b : ℕ) :
    ceilDiv (ceilDiv w a) b = ceilDiv w (a * b) := by
  by_cases hw : w = 0
  · simp [hw]
  · have hw' : 0 < w := by omega
    rw [ceilDiv_of_pos (ceilDiv_pos hw' a), ceilDiv_of_pos hw',
      ceilDiv_of_pos hw']
    simp only [Nat.add_sub_cancel_right]
    rw [Nat.div_div_eq_div_mul]

/-- The characteristic inequality for ordinary ceiling division. -/
theorem ceilDiv_le_iff (w q m : ℕ) (hq : 0 < q) :
    ceilDiv w q ≤ m ↔ w ≤ m * q := by
  by_cases hw : w = 0
  · simp [hw]
  · have hw' : 0 < w := by omega
    rw [ceilDiv_of_pos hw']
    constructor
    · intro h
      have hd : (w - 1) / q < m := by omega
      have hm : w - 1 < m * q := (Nat.div_lt_iff_lt_mul hq).mp hd
      omega
    · intro h
      have hm : w - 1 < m * q := by omega
      have hd : (w - 1) / q < m := (Nat.div_lt_iff_lt_mul hq).mpr hm
      omega

/-- The support count resulting from one ceiling-division compression per round. -/
def compressedWeight (q d : ℕ) : ℕ → ℕ
  | 0 => d
  | r + 1 => ceilDiv (compressedWeight q d r) q

theorem compressedWeight_eq_ceilDiv_pow (q d r : ℕ) :
    compressedWeight q d r = ceilDiv d (q ^ r) := by
  induction r with
  | zero => simp [compressedWeight]
  | succ r ih =>
      rw [compressedWeight, ih, ceilDiv_comp, pow_succ]

theorem compressedWeight_eq (q d r : ℕ) (hd : 0 < d) :
    compressedWeight q d r = (d - 1) / q ^ r + 1 := by
  rw [compressedWeight_eq_ceilDiv_pow, ceilDiv_of_pos hd]

theorem compressedWeight_pos (q d r : ℕ) (hd : 0 < d) :
    0 < compressedWeight q d r := by
  rw [compressedWeight_eq_ceilDiv_pow]
  exact ceilDiv_pos hd _

theorem compressedWeight_le_iff (q d r m : ℕ) (hq : 0 < q) :
    compressedWeight q d r ≤ m ↔ d ≤ m * q ^ r := by
  rw [compressedWeight_eq_ceilDiv_pow]
  exact ceilDiv_le_iff d (q ^ r) m (pow_pos hq r)

theorem clog_pos_of_two_le (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    0 < Nat.clog q d := by
  have hq' : 1 < q := by omega
  have hp : d ≤ q ^ Nat.clog q d :=
    (Nat.clog_le_iff_le_pow hq').mp (le_refl _)
  by_contra hn
  have hz : Nat.clog q d = 0 := by omega
  rw [hz] at hp
  simp only [pow_zero] at hp
  omega

theorem clog_eq_one_of_distance_le_arity (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d)
    (hdq : d ≤ q) : Nat.clog q d = 1 := by
  have hm : 0 < Nat.clog q d := clog_pos_of_two_le q d hq hd
  have hu : Nat.clog q d ≤ 1 := (Nat.clog_le_iff_le_pow (by omega : 1 < q)).mpr
    (by simpa only [pow_one] using hdq)
  omega

/-- `ceil(log_q d)-1` compression rounds leave at most `q` active sites. -/
theorem compressedWeight_at_clog_pred_le (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    compressedWeight q d (Nat.clog q d - 1) ≤ q := by
  have hq' : 1 < q := by omega
  have hp : d ≤ q ^ Nat.clog q d :=
    (Nat.clog_le_iff_le_pow hq').mp (le_refl _)
  have hm : 0 < Nat.clog q d := clog_pos_of_two_le q d hq hd
  have hs : Nat.clog q d - 1 + 1 = Nat.clog q d := by omega
  have hp' : d ≤ q ^ (Nat.clog q d - 1 + 1) := by
    rw [hs]
    exact hp
  rw [pow_succ] at hp'
  apply (compressedWeight_le_iff q d (Nat.clog q d - 1) q (by omega)).mpr
  simpa only [Nat.mul_comm] using hp'

/-- Compression, one rotation layer, and uncomputation give the stated count. -/
theorem synthesis_depth_count (m : ℕ) (hm : 0 < m) :
    (m - 1) + 1 + (m - 1) = 2 * m - 1 := by
  omega

theorem synthesis_depth_at_clog (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    (Nat.clog q d - 1) + 1 + (Nat.clog q d - 1) = criticalDepth q d := by
  unfold criticalDepth
  exact synthesis_depth_count _ (clog_pos_of_two_le q d hq hd)

end CriticalDepth.Arithmetic
