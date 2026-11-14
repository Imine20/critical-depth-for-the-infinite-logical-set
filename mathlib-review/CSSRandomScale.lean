import CSSRandomParameters
import Mathlib.Data.Nat.Choose.Bounds

/-!
Explicit elementary estimates for the polynomially scaled random CSS family.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

theorem twelve_pow_bound (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    cssSites R ≤ 2 ^ (R / 256) := by
  have haux (m : ℕ) (hm : 128 ≤ m) : 8192 * (m + 1) ≤ 2 ^ m := by
    induction m, hm using Nat.le_induction with
    | base => decide
    | succ m hm ih =>
        rw [pow_succ]
        have hstep : 8192 * (m + 1 + 1) ≤ 2 * (8192 * (m + 1)) := by omega
        exact hstep.trans (by simpa only [mul_comm] using Nat.mul_le_mul_left 2 ih)
  let m := R / 8192
  have hm : 128 ≤ m := by dsimp [m]; omega
  have hcap : R ≤ 8192 * (m + 1) := by dsimp [m]; omega
  have hRpow : R ≤ 2 ^ m := hcap.trans (haux m hm)
  unfold cssSites
  calc
    R ^ 12 ≤ (2 ^ m) ^ 12 := Nat.pow_le_pow_left hRpow 12
    _ = 2 ^ (m * 12) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (R / 256) := Nat.pow_le_pow_right (by decide) (by dsimp [m]; omega)

theorem natShells_le_mul_pow (n k : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range (k + 1), n.choose j) ≤ (k + 1) * n ^ k := by
  calc
    _ ≤ ∑ _j ∈ Finset.range (k + 1), n ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow _ _).trans
        (Nat.pow_le_pow_right hn (by have := Finset.mem_range.mp hj; omega))
    _ = _ := by simp

theorem natShells_le_power (n k m : ℕ) (hn : 0 < n) (hp : n ≤ 2 ^ m) (hk : k + 1 ≤ 2 ^ m) :
    (∑ j ∈ Finset.range (k + 1), n.choose j) ≤ 2 ^ (m * (k + 1)) := by
  calc
    _ ≤ (k + 1) * n ^ k := natShells_le_mul_pow n k hn
    _ ≤ 2 ^ m * (2 ^ m) ^ k := Nat.mul_le_mul hk (Nat.pow_le_pow_left hp _)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring

theorem css_x_check_scale (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    (R / 256) * (R * (cssXDimension R + 1) + 1) + cssXDimension R + R + 2 ≤ cssSites R ∧
    (R / 256) * (cssDistance R + 1) + R + 1 ≤ cssXDimension R := by
  have hr : 4 ≤ R := by omega
  have hp : 0 < R := by omega
  have hlim : R / 256 ≤ R := Nat.div_le_self _ _
  have h1 : 1 ≤ R ^ 4 := pow_pos hp _
  have h2 : 8 ≤ R ^ 4 := by
    exact (show 8 ≤ 4 ^ 4 by decide).trans (Nat.pow_le_pow_left hr _)
  have r2 : 4 ≤ R ^ 2 := by exact (show 4 ≤ 4 ^ 2 by decide).trans (Nat.pow_le_pow_left hr _)
  have r3 : 4 ≤ R ^ 3 := by exact (show 4 ≤ 4 ^ 3 by decide).trans (Nat.pow_le_pow_left hr _)
  have hmain : (R / 256) * (R * (R ^ 4 + 1) + 1) ≤ 4 * R ^ 6 := by
    have hmul := Nat.mul_le_mul_right (R * (R ^ 4 + 1) + 1) hlim
    have he : R * (R * (R ^ 4 + 1) + 1) = R ^ 6 + R ^ 2 + R := by ring
    rw [he] at hmul
    have h26 : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right hp (by decide)
    have h16 : R ≤ R ^ 6 := by simpa using Nat.pow_le_pow_right hp (by decide : 1 ≤ 6)
    omega
  have hfull : 6 * R ^ 6 ≤ R ^ 12 := by
    have h6 : 6 ≤ R ^ 6 := (show 6 ≤ 4 ^ 6 by decide).trans (Nat.pow_le_pow_left hr _)
    rw [show (12 : ℕ) = 6 + 6 by decide, pow_add]
    exact Nat.mul_le_mul_right _ h6
  have h46 : R ^ 4 ≤ R ^ 6 := Nat.pow_le_pow_right hp (by decide)
  have hRoom : R + 2 ≤ R ^ 6 := by
    have hmid : R + 2 ≤ R ^ 2 := by nlinarith
    exact hmid.trans (Nat.pow_le_pow_right hp (by decide))
  constructor
  · unfold cssSites cssXDimension
    omega
  · unfold cssDistance cssXDimension
    have h := Nat.mul_le_mul_right (R ^ 2 + 1) hlim
    have he : R * (R ^ 2 + 1) = R ^ 3 + R := by ring
    rw [he] at h
    have hf : 4 * R ^ 3 ≤ R ^ 4 := by
      rw [show R ^ 4 = R * R ^ 3 by ring]
      exact Nat.mul_le_mul_right _ hr
    have h13 : R + 1 ≤ R ^ 3 := by
      have hh : R + 1 ≤ R ^ 2 := by nlinarith
      exact hh.trans (Nat.pow_le_pow_right hp (by decide))
    omega

end CriticalDepth.Manuscript20261114.CSSCheckSpaces