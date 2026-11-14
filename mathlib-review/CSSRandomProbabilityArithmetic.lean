import CSSRandomScale
import CSSWeightBallCounts
import CSSCodeDimension

/-!
Finite probability estimates for the two check-distance bad events.
They use integer cardinalities throughout.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators

theorem binaryCheck_distance_bad_scaled (a k slack shellPrimal shellDual : ℕ) (ha : 0 < a)
    (hw : shellPrimal ≤ 2 ^ k) (hd : shellDual ≤ 2 ^ (a - (slack + 1)))
    (hadv : slack + 1 ≤ a)
    (N : ℕ) (hN : 2 ^ (k + a + (slack + 1)) ≤ N) :
    ((2 ^ a - 1) * shellPrimal * N ^ (a - 1) +
        shellDual * (N ^ a / 2 ^ a)) * 2 ^ slack ≤ N ^ a := by
  have h₁ : (2 ^ a - 1) * shellPrimal * N ^ (a - 1) * 2 ^ (slack + 1) ≤ N ^ a := by
    calc
      _ ≤ (2 ^ a * 2 ^ k * N ^ (a - 1)) * 2 ^ (slack + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.sub_le _ _) hw))
      _ = 2 ^ (k + a + (slack + 1)) * N ^ (a - 1) := by
        rw [pow_add, pow_add]
        ring
      _ ≤ N * N ^ (a - 1) := Nat.mul_le_mul_right _ hN
      _ = _ := by rw [← pow_succ', show a - 1 + 1 = a by omega]
  have h₂ : shellDual * (N ^ a / 2 ^ a) * 2 ^ (slack + 1) ≤ N ^ a := by
    calc
      _ ≤ 2 ^ (a - (slack + 1)) * (N ^ a / 2 ^ a) * 2 ^ (slack + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hd)
      _ = (N ^ a / 2 ^ a) * 2 ^ a := by
        have hpow : (2 : ℕ) ^ (a - (slack + 1)) * 2 ^ (slack + 1) = 2 ^ a := by
          rw [← pow_add, Nat.sub_add_cancel hadv]
        rw [mul_right_comm, hpow, mul_comm]
      _ ≤ _ := Nat.div_mul_le_self _ _
  rw [add_mul]
  rw [pow_succ, ← mul_assoc] at h₁ h₂
  omega

theorem plantWordOfWeight_exists (n d : ℕ) (hdn : d ≤ n) :
    ∃ p : BW n, wordWeight p = d := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using hdn)
  let p : BW n := fun i => if i ∈ S then 1 else 0
  refine ⟨p, ?_⟩
  have h : (Finset.univ.filter fun i => p i ≠ 0) = S := by
    ext i
    simp [p]
  have he : wordWeight p = (Finset.univ.filter fun i => p i ≠ 0).card := by
    unfold wordWeight
    apply congrArg Finset.card
    have hfg (d₁ d₂ : DecidablePred (fun i : Fin n => p i ≠ 0)) :
        @Finset.filter _ _ d₁ Finset.univ = @Finset.filter _ _ d₂ Finset.univ :=
      @Finset.filter_congr_decidable _ _ (fun i : Fin n => p i ≠ 0) d₁ d₂
    exact hfg _ _
  rw [he, h, hS]

theorem css_z_check_scale (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    (R / 256) * (cssDeletionThreshold R + 1) + cssZDimension R + R + 2 ≤
      cssSites R - cssXDimension R ∧
    (R / 256) * (R * (cssXDimension R + 1) + 1) + R + 1 ≤ cssZDimension R ∧
    2 * cssSites R ≤ 5 * (cssSites R - cssXDimension R - cssZDimension R) := by
  have hR4 : 4 ≤ R := by omega
  have hp : 0 < R := by omega
  have hn4 : R ^ 4 ≤ R ^ 6 := Nat.pow_le_pow_right hp (by decide)
  have hn8 : R ^ 6 ≤ R ^ 8 := Nat.pow_le_pow_right hp (by decide)
  have hn1 : R ≤ R ^ 8 := by simpa using Nat.pow_le_pow_right hp (by decide : 1 ≤ 8)
  have hT := cssDeletionThreshold_le_four_mul_pow R (by omega)
  have hd : R / 256 ≤ R := Nat.div_le_self _ _
  have hc : (R / 256) * (cssDeletionThreshold R + 1) ≤ 5 * R ^ 8 := by
    calc
      _ ≤ R * (4 * R ^ 7 + 1) := Nat.mul_le_mul hd (Nat.succ_le_succ hT)
      _ = 4 * R ^ 8 + R := by ring
      _ ≤ _ := by omega
  have hz : 8 * R ^ 8 ≤ R ^ 12 := by
    have h4 : 8 ≤ R ^ 4 := (show 8 ≤ 4 ^ 4 by decide).trans (Nat.pow_le_pow_left hR4 _)
    rw [show (12 : ℕ) = 4 + 8 by decide, pow_add]
    exact Nat.mul_le_mul_right _ h4
  have hrs : (R / 256) * 256 ≤ R := Nat.div_mul_le_self _ _
  have hr2 : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right hp (by decide)
  have hr6 : R ≤ R ^ 6 := by simpa using Nat.pow_le_pow_right hp (by decide : 1 ≤ 6)
  have hscaled : 256 * ((R / 256) * (R * (R ^ 4 + 1) + 1)) ≤ 3 * R ^ 6 := by
    calc
      _ = ((R / 256) * 256) * (R * (R ^ 4 + 1) + 1) := by ring
      _ ≤ R * (R * (R ^ 4 + 1) + 1) := Nat.mul_le_mul_right _ hrs
      _ = R ^ 6 + R ^ 2 + R := by ring
      _ ≤ _ := by omega
  have hR6 : 2 * (R + 1) ≤ R ^ 6 := by
    have h : R ^ 2 ≤ R ^ 6 := hr2
    have h' : 2 * (R + 1) ≤ R ^ 2 := by nlinarith
    exact h'.trans h
  have hh₁ : R ^ 4 ≤ R ^ 12 := hn4.trans (hn8.trans (by omega))
  have hh₂ : R ^ 6 ≤ R ^ 12 - R ^ 4 := by omega
  unfold cssSites cssXDimension cssZDimension
  omega

#print axioms binaryCheck_distance_bad_scaled
#print axioms plantWordOfWeight_exists
#print axioms css_z_check_scale

end CriticalDepth.Manuscript20261114.CSSCheckSpaces