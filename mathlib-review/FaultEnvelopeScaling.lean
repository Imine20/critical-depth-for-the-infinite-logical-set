import FaultDepthArithmetic

/-!
# Size of the fault exponent envelopes

These are arithmetic estimates for the envelopes in Figure 2 and the final
comparison in Theorem 3(2). They apply independently of the code construction.
-/

namespace CriticalDepth.FaultDepthArithmetic

open CriticalDepth.Arithmetic

private theorem ceilDiv_eq_realCeil (d s : ℕ) (hs : 0 < s) :
    ceilDiv d s = ⌈(d : ℝ) / (s : ℝ)⌉₊ := by
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have compareTo (m : ℕ) : ceilDiv d s ≤ m ↔ ⌈(d : ℝ) / (s : ℝ)⌉₊ ≤ m := by
    rw [ceilDiv_le_iff d s m hs, Nat.ceil_le, div_le_iff₀ hsReal]
    norm_cast
  exact le_antisymm ((compareTo _).mpr le_rfl) ((compareTo _).mp le_rfl)

theorem ceilDiv_realBounds (d s : ℕ) (hs : 0 < s) :
    (d : ℝ) / (s : ℝ) ≤ (ceilDiv d s : ℝ) ∧
    (ceilDiv d s : ℝ) < (d : ℝ) / (s : ℝ) + 1 := by
  rw [ceilDiv_eq_realCeil d s hs]
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩

/-- At fixed arity and depth both envelopes have explicit linear bounds in d. -/
theorem envelopes_linearBounds (q d h : ℕ) (hq : 1 ≤ q) :
    (d : ℝ) / ((q : ℝ) ^ h + q) ≤ (lowerEnvelope q d h : ℝ) ∧
    (lowerEnvelope q d h : ℝ) ≤ 2 * d ∧
    (d : ℝ) / (2 * (q : ℝ) ^ ceilHalf h) ≤ (upperEnvelope q d h : ℝ) ∧
    (upperEnvelope q d h : ℝ) ≤ 2 * d := by
  have bounds (s : ℕ) (hs : 0 < s) :
      (d : ℝ) / s ≤ (ceilDiv d s : ℝ) ∧ (ceilDiv d s : ℝ) ≤ 2 * d := by
    refine ⟨(ceilDiv_realBounds d s hs).1, ?_⟩
    have hds : d ≤ d * s := by simpa using Nat.mul_le_mul_left d hs
    have hceil : ceilDiv d s ≤ d := (ceilDiv_le_iff d s d hs).mpr hds
    have hceilReal : (ceilDiv d s : ℝ) ≤ d := by exact_mod_cast hceil
    linarith
  have lower := bounds (q ^ h + q) (by omega)
  have upper := bounds (2 * q ^ ceilHalf h) (by positivity)
  exact ⟨by exact_mod_cast lower.1, lower.2, by exact_mod_cast upper.1, upper.2⟩

/-- At h = t and d = q^(2t), the finite correction to the lower envelope is
q - 1 once q^t + q exceeds q^2. -/
theorem lowerEnvelope_midpoint_exact (q t : ℕ) (hq : 2 ≤ q)
    (large : q ^ 2 < q ^ t + q) :
    lowerEnvelope q (q ^ (2 * t)) t = q ^ t - q + 1 := by
  have hN : q ≤ q ^ t := by
    cases t with
    | zero =>
      rw [pow_zero] at large
      nlinarith [sq_nonneg ((q : ℤ) - 2)]
    | succ t =>
      rw [pow_succ]
      have hp : 1 ≤ q ^ t := pow_pos (by omega : 0 < q) _
      simpa only [one_mul] using Nat.mul_le_mul_right q hp
  rw [two_mul, pow_add]
  set r := q ^ t with hr
  have hpos : 0 < r + q := by omega
  have hp : 0 < q ^ 2 := by positivity
  change ceilDiv (r * r) (r + q) = r - q + 1
  have hsplit : r - q + q = r := Nat.sub_add_cancel hN
  have hdiv : (r - q) * (r + q) + q ^ 2 = r * r := by
    calc
      _ = ((r - q) + q) * ((r - q) + q) := by
        conv_lhs => arg 1; arg 2; arg 1; rw [← hsplit]
        ring
      _ = r * r := by rw [hsplit]
  apply le_antisymm
  · apply (ceilDiv_le_iff _ _ _ hpos).mpr
    rw [add_mul, one_mul, ← hdiv]
    omega
  · have hlt : r - q < ceilDiv (r * r) (r + q) := by
      by_contra! hle
      have := (ceilDiv_le_iff _ _ _ hpos).mp hle
      omega
    omega

/-- Bounds with constants depending only on q for the d^(3/4) comparison at
h = t and d = q^(2t), including both parities of t. -/
theorem upperEnvelope_midpoint_threeQuarterBounds (q t : ℕ) (hq : 2 ≤ q) :
    (q ^ (2 * t) : ℝ) ^ (3 / 4 : ℝ) / (2 * q) ≤
      (upperEnvelope q (q ^ (2 * t)) t : ℝ) ∧
    (upperEnvelope q (q ^ (2 * t)) t : ℝ) ≤
      2 * (q ^ (2 * t) : ℝ) ^ (3 / 4 : ℝ) := by
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := by linarith
  have hbase : (1 : ℝ) ≤ q := by linarith
  have hloNat : t ≤ 2 * ceilHalf t := by unfold ceilHalf; omega
  have hhiNat : 2 * ceilHalf t ≤ t + 2 := by unfold ceilHalf; omega
  have hloCast : (t : ℝ) ≤ 2 * (ceilHalf t : ℝ) := by exact_mod_cast hloNat
  have hhiCast : 2 * (ceilHalf t : ℝ) ≤ (t : ℝ) + 2 := by exact_mod_cast hhiNat
  have hlo : (q : ℝ) ^ ((t : ℝ) / 2) ≤ (q : ℝ) ^ ceilHalf t := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hhi : (q : ℝ) ^ ceilHalf t ≤ (q : ℝ) ^ ((t : ℝ) / 2) * q := by
    rw [← Real.rpow_natCast]
    conv_rhs => arg 2; rw [← Real.rpow_one (q : ℝ)]
    rw [← Real.rpow_add hqPos]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hpow : (q ^ (2 * t) : ℝ) ^ (3 / 4 : ℝ) = (q : ℝ) ^ (3 * (t : ℝ) / 2) := by
    rw [← Real.rpow_natCast_mul hqPos.le]
    congr 1
    push_cast
    ring
  have hproduct : (q : ℝ) ^ (3 * (t : ℝ) / 2) * (q : ℝ) ^ ((t : ℝ) / 2) =
      (q : ℝ) ^ (2 * t) := by
    rw [← Real.rpow_add hqPos, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hr : (0 : ℝ) ≤ (q : ℝ) ^ (3 * (t : ℝ) / 2) := Real.rpow_nonneg hqPos.le _
  have hrOne : (1 : ℝ) ≤ (q : ℝ) ^ (3 * (t : ℝ) / 2) := by
    rw [← Real.rpow_zero (q : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by positivity)
  have hbound := ceilDiv_realBounds (q ^ (2 * t)) (2 * q ^ ceilHalf t) (by positivity)
  unfold upperEnvelope
  rw [hpow]
  push_cast at hbound
  have hden : (0 : ℝ) < 2 * (q : ℝ) ^ ceilHalf t := by positivity
  have hdivUpper : (q : ℝ) ^ (2 * t) / (2 * (q : ℝ) ^ ceilHalf t) ≤
      (q : ℝ) ^ (3 * (t : ℝ) / 2) := by
    apply (div_le_iff₀ hden).mpr
    rw [← hproduct]
    exact mul_le_mul_of_nonneg_left (by linarith [show 0 ≤ (q : ℝ) ^ ceilHalf t by positivity]) hr
  have hdivLower : (q : ℝ) ^ (3 * (t : ℝ) / 2) / (2 * q) ≤
      (q : ℝ) ^ (2 * t) / (2 * (q : ℝ) ^ ceilHalf t) := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    rw [← hproduct]
    calc
      _ ≤ (q : ℝ) ^ (3 * (t : ℝ) / 2) *
          (2 * ((q : ℝ) ^ ((t : ℝ) / 2) * q)) :=
        mul_le_mul_of_nonneg_left (by linarith) hr
      _ = _ := by ring
  exact ⟨hdivLower.trans hbound.1, by linarith [hbound.2]⟩

theorem envelopes_midpoint_strict (q t : ℕ) (hq : 2 ≤ q) (ht : 4 ≤ t) :
    lowerEnvelope q (q ^ (2 * t)) t < upperEnvelope q (q ^ (2 * t)) t := by
  rw [two_mul, pow_add]
  have hqPos : 0 < q := by omega
  have hpowPos : 0 < q ^ t := pow_pos hqPos _
  have hsmall : ceilHalf t + 2 ≤ t := by unfold ceilHalf; omega
  have htwice : 2 * q ^ ceilHalf t < q ^ t := by
    have hqSq : 2 < q ^ 2 := by nlinarith
    have hlt := Nat.mul_lt_mul_of_pos_left hqSq (pow_pos hqPos (ceilHalf t))
    rw [← pow_add, mul_comm _ 2] at hlt
    exact hlt.trans_le (Nat.pow_le_pow_right hqPos hsmall)
  have hlow : lowerEnvelope q (q ^ t * q ^ t) t ≤ q ^ t := by
    exact (ceilDiv_le_iff _ _ _ (by omega)).mpr
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  have hupp : q ^ t < upperEnvelope q (q ^ t * q ^ t) t := by
    by_contra! hle
    exact (not_le_of_gt (Nat.mul_lt_mul_of_pos_left htwice hpowPos))
      ((ceilDiv_le_iff _ _ _ (by positivity)).mp hle)
  exact hlow.trans_lt hupp

/-- At h = t the lower envelope is of order sqrt(d), with d = q^(2t)
and a constant independent of q once q^t ≥ q. -/
theorem lowerEnvelope_midpoint_squareRootBounds (q t : ℕ) (hq : 1 ≤ q) (ht : 1 ≤ t) :
    Real.sqrt ((q : ℝ) ^ (2 * t)) / 2 ≤ (lowerEnvelope q (q ^ (2 * t)) t : ℝ) ∧
    (lowerEnvelope q (q ^ (2 * t)) t : ℝ) ≤ Real.sqrt ((q : ℝ) ^ (2 * t)) := by
  have hpow : q ≤ q ^ t := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) ht
  have hpowReal : (q : ℝ) ≤ (q : ℝ) ^ t := by exact_mod_cast hpow
  have hpos : 0 < q ^ t + q := by omega
  have hposReal : 0 < (q : ℝ) ^ t + q := by positivity
  have hroot : Real.sqrt ((q : ℝ) ^ (2 * t)) = (q : ℝ) ^ t := by
    rw [two_mul, pow_add, ← pow_two, Real.sqrt_sq (by positivity)]
  rw [hroot, two_mul, pow_add]
  have hl := (ceilDiv_realBounds (q ^ t * q ^ t) (q ^ t + q) hpos).1
  push_cast at hl
  refine ⟨le_trans ?_ hl, ?_⟩
  · apply (le_div_iff₀ hposReal).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpowReal (by positivity : 0 ≤ (q : ℝ) ^ t)]
  · have hceil : lowerEnvelope q (q ^ t * q ^ t) t ≤ q ^ t :=
      (ceilDiv_le_iff _ _ _ hpos).mpr (by
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
    exact_mod_cast hceil

#print axioms lowerEnvelope_midpoint_squareRootBounds
#print axioms envelopes_linearBounds
#print axioms lowerEnvelope_midpoint_exact
#print axioms upperEnvelope_midpoint_threeQuarterBounds
#print axioms envelopes_midpoint_strict

end CriticalDepth.FaultDepthArithmetic