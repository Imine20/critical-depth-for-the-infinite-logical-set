import CriticalDepthMathlib

/-!
# Depth and fault-count arithmetic for manuscript 20261114v3

These lemmas give the arithmetic of the two-frame support estimate and the
critical depths at which the manuscript's exponent envelopes reach one.
The support counts are hypotheses here. The circuit semantics, recovery, and
probability estimates are separate obligations.
-/

namespace CriticalDepth.FaultDepthArithmetic

open CriticalDepth.Arithmetic
open scoped BigOperators

def lowerEnvelope (q d h : ℕ) : ℕ := ceilDiv d (q ^ h + q)

def upperEnvelope (q d h : ℕ) : ℕ := ceilDiv d (2 * q ^ ceilHalf h)

def lowerOnset (q d : ℕ) : ℕ := Nat.clog q (d - q)

def upperOnset (q d : ℕ) : ℕ := criticalDepth q (ceilDiv d 2)

/-- The input and output cone exponents of a location in layer `j` are
`j` and `h - j + 1`. -/
theorem layerConeSum_le (q h j : ℕ) (hq : 1 ≤ q) (hj : 1 ≤ j) (hjh : j ≤ h) :
    q ^ j + q ^ (h - j + 1) ≤ q ^ h + q := by
  have hx : 1 ≤ q ^ (j - 1) := pow_pos (by omega : 0 < q) _
  have hy : 1 ≤ q ^ (h - j) := pow_pos (by omega : 0 < q) _
  have hx' : (1 : ℤ) ≤ (q : ℤ) ^ (j - 1) := by exact_mod_cast hx
  have hy' : (1 : ℤ) ≤ (q : ℤ) ^ (h - j) := by exact_mod_cast hy
  have hmul : q ^ (j - 1) + q ^ (h - j) ≤ q ^ (j - 1) * q ^ (h - j) + 1 := by
    have hh := mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy')
    have hh' : (q : ℤ) ^ (j - 1) + q ^ (h - j) ≤
        (q : ℤ) ^ (j - 1) * q ^ (h - j) + 1 := by
      nlinarith only [hh]
    exact_mod_cast hh'
  have hfront : q ^ j = q ^ (j - 1) * q := by
    rw [← pow_succ, show j - 1 + 1 = j by omega]
  calc
    q ^ j + q ^ (h - j + 1) = (q ^ (j - 1) + q ^ (h - j)) * q := by
      rw [hfront, pow_succ q (h - j), add_mul]
    _ ≤ (q ^ (j - 1) * q ^ (h - j) + 1) * q := Nat.mul_le_mul_right _ hmul
    _ = q ^ h + q := by
      rw [← pow_add, show j - 1 + (h - j) = h - 1 by omega,
        add_mul, one_mul, ← pow_succ, show h - 1 + 1 = h by omega]

/-- Tag the locations by history before forming the sums, so the same physical
location in two histories contributes twice to the support bound. -/
theorem pairedHistories_oneFrame_lt {ι : Type*} (locations : Finset ι)
    (q d h r : ℕ) (layer inputSize outputSize : ι → ℕ)
    (hq : 1 ≤ q) (hcard : locations.card ≤ 2 * r)
    (hr : r < lowerEnvelope q d h)
    (hlayer : ∀ i ∈ locations, 1 ≤ layer i ∧ layer i ≤ h)
    (hinput : ∀ i ∈ locations, inputSize i ≤ q ^ layer i)
    (houtput : ∀ i ∈ locations, outputSize i ≤ q ^ (h - layer i + 1)) :
    (∑ i ∈ locations, inputSize i) < d ∨ (∑ i ∈ locations, outputSize i) < d := by
  have hden : 0 < q ^ h + q := by omega
  have hrd : r * (q ^ h + q) < d := by
    apply lt_of_not_ge
    intro hge
    exact (not_le_of_gt hr) ((ceilDiv_le_iff _ _ _ hden).mpr hge)
  have hsum : (∑ i ∈ locations, (inputSize i + outputSize i)) ≤
      locations.card * (q ^ h + q) := by
    calc
      _ ≤ ∑ _i ∈ locations, (q ^ h + q) :=
        Finset.sum_le_sum fun i hi =>
          (Nat.add_le_add (hinput i hi) (houtput i hi)).trans
            (layerConeSum_le q h (layer i) hq (hlayer i hi).1 (hlayer i hi).2)
      _ = _ := Finset.sum_const_nat fun _ _ => rfl
  rw [Finset.sum_add_distrib] at hsum
  have htotal := hsum.trans (Nat.mul_le_mul_right (q ^ h + q) hcard)
  rw [Nat.mul_assoc] at htotal
  by_cases hi : (∑ i ∈ locations, inputSize i) < d
  · exact Or.inl hi
  · right
    omega

/-- This bound applies when both frame estimates refer to the same support
size, as happens when the total physical unitary is an on-site product. -/
theorem shorterCone_le (q h j size : ℕ) (hq : 1 ≤ q) (hj : 1 ≤ j) (hjh : j ≤ h)
    (hinput : size ≤ q ^ j) (houtput : size ≤ q ^ (h - j + 1)) :
    size ≤ q ^ ceilHalf h := by
  have hq' : 0 < q := by omega
  by_cases ha : j ≤ ceilHalf h
  · exact hinput.trans (Nat.pow_le_pow_right hq' ha)
  · have hb : h - j + 1 ≤ ceilHalf h := by
      have hm := layer_min_le_ceilHalf h j hj hjh
      rw [min_eq_right (by unfold ceilHalf at ha; omega)] at hm
      exact hm
    exact houtput.trans (Nat.pow_le_pow_right hq' hb)

theorem lowerEnvelope_le_upperEnvelope (q d h : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h) :
    lowerEnvelope q d h ≤ upperEnvelope q d h := by
  have hq' : 0 < q := by omega
  have hj : 1 ≤ ceilHalf h := by unfold ceilHalf; omega
  have hjh : ceilHalf h ≤ h := by unfold ceilHalf; omega
  have hother : ceilHalf h ≤ h - ceilHalf h + 1 := by unfold ceilHalf; omega
  have hden : 2 * q ^ ceilHalf h ≤ q ^ h + q := by
    rw [two_mul]
    exact (Nat.add_le_add_left (Nat.pow_le_pow_right hq' hother) _).trans
      (layerConeSum_le q h (ceilHalf h) hq hj hjh)
  have hp : 0 < 2 * q ^ ceilHalf h := Nat.mul_pos (by decide) (pow_pos hq' _)
  have hbound : d ≤ upperEnvelope q d h * (2 * q ^ ceilHalf h) :=
    (ceilDiv_le_iff _ _ _ hp).mp (le_refl _)
  exact (ceilDiv_le_iff _ _ _ (by omega)).mpr
    (hbound.trans (Nat.mul_le_mul_left _ hden))

/-- Splitting the midpoint locations between two histories gives the upper
envelope's denominator, including the case of an odd number of blocks. -/
theorem midpointHistoryCount (q d h : ℕ) :
    ceilDiv (ceilDiv d (q ^ ceilHalf h)) 2 = upperEnvelope q d h := by
  rw [upperEnvelope, ceilDiv_comp, mul_comm (q ^ ceilHalf h) 2]

theorem lowerEnvelope_eq_one_iff (q d h : ℕ) (hq : 2 ≤ q) (hd : 2 * q < d) :
    lowerEnvelope q d h = 1 ↔ lowerOnset q d ≤ h := by
  have hd' : 0 < d := by omega
  have hp : 0 < q ^ h + q := by omega
  have hpos : 0 < lowerEnvelope q d h := ceilDiv_pos hd' _
  have hbase : 1 < q := by omega
  rw [show lowerEnvelope q d h = 1 ↔ lowerEnvelope q d h ≤ 1 by omega]
  unfold lowerEnvelope lowerOnset
  rw [ceilDiv_le_iff _ _ _ hp, one_mul, Nat.clog_le_iff_le_pow hbase]
  omega

theorem upperEnvelope_eq_one_iff (q d h : ℕ) (hq : 2 ≤ q) (hd : 2 * q < d) :
    upperEnvelope q d h = 1 ↔ upperOnset q d ≤ h := by
  have hq' : 0 < q := by omega
  have hd' : 0 < d := by omega
  have hp : 0 < 2 * q ^ ceilHalf h := Nat.mul_pos (by decide) (pow_pos hq' _)
  have hpos : 0 < upperEnvelope q d h := ceilDiv_pos hd' _
  rw [show upperEnvelope q d h = 1 ↔ upperEnvelope q d h ≤ 1 by omega]
  unfold upperEnvelope upperOnset
  have hth : criticalDepth q (ceilDiv d 2) ≤ h ↔ ceilDiv d 2 ≤ q ^ ceilHalf h := by
    simpa only [not_lt] using not_congr (below_threshold_iff q (ceilDiv d 2) h hq)
  rw [ceilDiv_le_iff _ _ _ hp, one_mul, hth]
  rw [ceilDiv_le_iff _ _ _ (by decide : 0 < (2 : ℕ)), mul_comm (q ^ ceilHalf h) 2]

theorem lowerOnset_eq_log (q d : ℕ) (hqd : q ≤ d) :
    lowerOnset q d = ⌈Real.logb (q : ℝ) ((d : ℝ) - q)⌉₊ := by
  unfold lowerOnset
  rw [← Nat.cast_sub hqd, Real.natCeil_logb_natCast]

theorem upperOnset_eq_log (q d : ℕ) (hq : 2 ≤ q) (hd : 0 < d) :
    upperOnset q d = 2 * ⌈Real.logb (q : ℝ) ((d : ℝ) / 2)⌉₊ - 1 := by
  have hb : 1 < q := by omega
  have hb' : (1 : ℝ) < q := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd'' : (0 : ℝ) < (d : ℝ) / 2 := div_pos hd' (by norm_num)
  have hiff (k : ℕ) :
      Nat.clog q (ceilDiv d 2) ≤ k ↔ ⌈Real.logb (q : ℝ) ((d : ℝ) / 2)⌉₊ ≤ k := by
    rw [Nat.clog_le_iff_le_pow hb, ceilDiv_le_iff _ _ _ (by decide : 0 < (2 : ℕ)),
      Nat.ceil_le, Real.logb_le_iff_le_rpow hb' hd'', Real.rpow_natCast,
      div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    norm_cast
  have heq : Nat.clog q (ceilDiv d 2) = ⌈Real.logb (q : ℝ) ((d : ℝ) / 2)⌉₊ :=
    le_antisymm ((hiff _).mpr (le_refl _)) ((hiff _).mp (le_refl _))
  simp only [upperOnset, criticalDepth, heq]

theorem onset_order_and_gap (q d : ℕ) (hq : 2 ≤ q) (hd : 2 * q < d) :
    lowerOnset q d ≤ upperOnset q d ∧ upperOnset q d ≤ criticalDepth q d ∧
    (criticalDepth q d - upperOnset q d = 0 ∨ criticalDepth q d - upperOnset q d = 2) := by
  have hb : 1 < q := by omega
  have hd' : 0 < d := by omega
  have hd₂ : 2 ≤ ceilDiv d 2 := by
    by_contra! h
    have := (ceilDiv_le_iff d 2 1 (by decide)).mp (by omega : ceilDiv d 2 ≤ 1)
    omega
  have hup_pos : 1 ≤ upperOnset q d := by
    have := clog_pos_of_two_le q (ceilDiv d 2) hq hd₂
    unfold upperOnset criticalDepth
    omega
  have hu : upperEnvelope q d (upperOnset q d) = 1 :=
    (upperEnvelope_eq_one_iff q d _ hq hd).mpr (le_refl _)
  have hl : lowerEnvelope q d (upperOnset q d) = 1 := by
    have hle := lowerEnvelope_le_upperEnvelope q d (upperOnset q d) (by omega) hup_pos
    have hpos : 0 < lowerEnvelope q d (upperOnset q d) := ceilDiv_pos hd' _
    omega
  have hc₁ : Nat.clog q (ceilDiv d 2) ≤ Nat.clog q d :=
    Nat.clog_mono_right _ ((ceilDiv_le_iff _ _ _ (by decide)).mpr (by omega))
  have hc₂ : Nat.clog q d ≤ Nat.clog q (ceilDiv d 2) + 1 := by
    have hbound : ceilDiv d 2 ≤ q ^ Nat.clog q (ceilDiv d 2) :=
      (Nat.clog_le_iff_le_pow hb).mp (le_refl _)
    have hceil : d ≤ ceilDiv d 2 * 2 :=
      (ceilDiv_le_iff _ _ _ (by decide)).mp (le_refl _)
    apply (Nat.clog_le_iff_le_pow hb).mpr
    rw [pow_succ]
    exact hceil.trans ((Nat.mul_le_mul_right 2 hbound).trans (Nat.mul_le_mul_left _ hq))
  have hcpos := clog_pos_of_two_le q (ceilDiv d 2) hq hd₂
  refine ⟨(lowerEnvelope_eq_one_iff q d _ hq hd).mp hl, ?_, ?_⟩
  · unfold upperOnset criticalDepth
    omega
  · unfold upperOnset criticalDepth
    omega

#print axioms layerConeSum_le
#print axioms pairedHistories_oneFrame_lt
#print axioms shorterCone_le
#print axioms lowerEnvelope_le_upperEnvelope
#print axioms midpointHistoryCount
#print axioms lowerEnvelope_eq_one_iff
#print axioms upperEnvelope_eq_one_iff
#print axioms lowerOnset_eq_log
#print axioms upperOnset_eq_log
#print axioms onset_order_and_gap

end CriticalDepth.FaultDepthArithmetic
