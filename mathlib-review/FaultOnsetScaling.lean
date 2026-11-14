import FaultEnvelopeScaling

/-!
# Square-root scaling at the lower fault onset
-/

namespace CriticalDepth.FaultDepthArithmetic

open CriticalDepth.Arithmetic Filter Asymptotics

/-- At the depth where the lower envelope first equals one, the upper
envelope remains comparable to the square root of the distance. -/
theorem upperEnvelope_lowerOnset_squareRootBounds (q d : ℕ)
    (hq : 2 ≤ q) (hd : 2 * q < d) :
    Real.sqrt (d : ℝ) / (2 * (q : ℝ)) ≤ (upperEnvelope q d (lowerOnset q d) : ℝ) ∧
    (upperEnvelope q d (lowerOnset q d) : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by
  let h := lowerOnset q d
  let S := q ^ ceilHalf h
  let r := Real.sqrt (d : ℝ)
  have hqPos : 0 < q := by omega
  have hbase : 1 < q := by omega
  have hh : 0 < h := clog_pos_of_two_le q (d - q) hq (by omega)
  have hpow : d - q ≤ q ^ h :=
    (Nat.clog_le_iff_le_pow hbase).mp (le_refl h)
  have hpred : q ^ (h - 1) < d - q := by
    by_contra! hb
    have hle : h ≤ h - 1 :=
      (Nat.clog_le_iff_le_pow hbase).mpr hb
    omega
  have hhalfLo : h ≤ ceilHalf h * 2 := by unfold ceilHalf; omega
  have hhalfHi : ceilHalf h * 2 ≤ h + 1 := by unfold ceilHalf; omega
  have hSsq : S ^ 2 = q ^ (ceilHalf h * 2) := by rw [pow_mul]
  have hSsqLo : d ≤ 2 * S ^ 2 := by
    have hlo := hpow.trans (Nat.pow_le_pow_right hqPos hhalfLo)
    rw [← hSsq] at hlo
    omega
  have hSsqHi : S ^ 2 ≤ q ^ 2 * d := calc
    S ^ 2 = q ^ (ceilHalf h * 2) := hSsq
    _ ≤ q ^ (h + 1) := Nat.pow_le_pow_right hqPos hhalfHi
    _ = q ^ 2 * q ^ (h - 1) := by
      rw [← pow_add, show 2 + (h - 1) = h + 1 by omega]
    _ ≤ q ^ 2 * d := Nat.mul_le_mul_left _ (by omega)
  have hSpos : 0 < S := pow_pos hqPos _
  have hSposR : (0 : ℝ) < S := by exact_mod_cast hSpos
  have hrPos : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hrSq : r ^ 2 = (d : ℝ) := Real.sq_sqrt (by positivity)
  have hrOne : 1 ≤ r := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d by exact_mod_cast (show 1 ≤ d by omega))
  have hqPosR : (0 : ℝ) < q := by exact_mod_cast hqPos
  have hSsqLoR : (d : ℝ) ≤ 2 * (S : ℝ) ^ 2 := by exact_mod_cast hSsqLo
  have hSsqHiR : (S : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 * d := by exact_mod_cast hSsqHi
  have hrLe : r ≤ 2 * (S : ℝ) := by
    apply le_of_not_gt
    intro hb
    have hpos := mul_pos (sub_pos.mpr hb)
      (add_pos_of_pos_of_nonneg hrPos (by positivity : (0 : ℝ) ≤ 2 * (S : ℝ)))
    nlinarith only [hpos, hrSq, hSsqLoR, sq_nonneg (S : ℝ)]
  have hSLe : (S : ℝ) ≤ (q : ℝ) * r := by
    apply le_of_not_gt
    intro hb
    have hpos := mul_pos (sub_pos.mpr hb)
      (add_pos_of_pos_of_nonneg hSposR (mul_nonneg hqPosR.le hrPos.le))
    have hqrSq : ((q : ℝ) * r) ^ 2 = (q : ℝ) ^ 2 * d := by rw [mul_pow, hrSq]
    nlinarith only [hpos, hqrSq, hSsqHiR]
  have hden : (0 : ℝ) < 2 * (S : ℝ) := mul_pos (by norm_num) hSposR
  have hdenq : (0 : ℝ) < 2 * (q : ℝ) := mul_pos (by norm_num) hqPosR
  have hdivLo : r / (2 * (q : ℝ)) ≤ (d : ℝ) / (2 * (S : ℝ)) := by
    apply (div_le_div_iff₀ hdenq hden).mpr
    calc
      r * (2 * (S : ℝ)) ≤ r * (2 * ((q : ℝ) * r)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSLe (by norm_num)) hrPos.le
      _ = r ^ 2 * (2 * (q : ℝ)) := by ring
      _ = (d : ℝ) * (2 * (q : ℝ)) := by rw [hrSq]
  have hdivHi : (d : ℝ) / (2 * (S : ℝ)) ≤ r := by
    apply (div_le_iff₀ hden).mpr
    simpa only [← pow_two, hrSq] using mul_le_mul_of_nonneg_left hrLe hrPos.le
  have hceil := ceilDiv_realBounds d (2 * S) (Nat.mul_pos (by decide) hSpos)
  push_cast at hceil
  change r / (2 * (q : ℝ)) ≤ (ceilDiv d (2 * S) : ℝ) ∧ (ceilDiv d (2 * S) : ℝ) ≤ 2 * r
  exact ⟨hdivLo.trans hceil.1, by linarith [hceil.2, hdivHi, hrOne]⟩

/-- Fixing the native arity makes the upper envelope at the lower onset
a Big Theta function of the square root of the distance. -/
theorem upperEnvelope_lowerOnset_isTheta (q : ℕ) (hq : 2 ≤ q) :
    (fun d : ℕ => (upperEnvelope q d (lowerOnset q d) : ℝ)) =Θ[atTop]
      (fun d : ℕ => Real.sqrt (d : ℝ)) := by
  refine ⟨isBigO_iff.mpr ⟨2, ?_⟩, isBigO_iff.mpr ⟨2 * (q : ℝ), ?_⟩⟩
  · filter_upwards [eventually_ge_atTop (2 * q + 1)] with d hd
    have h := (upperEnvelope_lowerOnset_squareRootBounds q d hq (by omega)).2
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (upperEnvelope q d (lowerOnset q d) : ℝ))] using h
  · filter_upwards [eventually_ge_atTop (2 * q + 1)] with d hd
    have h := (upperEnvelope_lowerOnset_squareRootBounds q d hq (by omega)).1
    have hc : (0 : ℝ) < 2 * (q : ℝ) := by positivity
    have hl := (div_le_iff₀ hc).mp h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (upperEnvelope q d (lowerOnset q d) : ℝ)), mul_comm (2 * (q : ℝ))] using hl

#print axioms upperEnvelope_lowerOnset_squareRootBounds
#print axioms upperEnvelope_lowerOnset_isTheta

end CriticalDepth.FaultDepthArithmetic