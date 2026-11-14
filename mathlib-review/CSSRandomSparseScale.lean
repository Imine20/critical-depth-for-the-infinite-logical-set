import CSSRandomProbabilityArithmetic
import CSSRandomShellScale
import CSSSparseLinearBudget

/-!
Explicit polynomial bounds used by the sparse-matrix union estimates.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

theorem css_bound_for_matrix_shells (R w : ℕ) (hR : 2 ^ 20 ≤ R)
    (hw : w + 1 ≤ cssSites R) :
    cssSites R * ((w + 1) * cssSites R ^ w) ≤ 2 ^ ((R / 256) * (w + 2)) := by
  have hn := twelve_pow_bound R hR
  calc
    _ ≤ 2 ^ (R / 256) * (2 ^ (R / 256) * (2 ^ (R / 256)) ^ w) :=
      Nat.mul_le_mul hn (Nat.mul_le_mul (hw.trans hn) (Nat.pow_le_pow_left hn _))
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring

theorem css_symmetric_row_slack (R u : ℕ) (hR : 2 ^ 20 ≤ R) (hu : 0 < u) :
    (R / 256 * (R + 3)) * u + (R / 256 + R + 1) ≤ u * cssXDimension R / (20 * (R + 1)) := by
  have hp : 0 < R := by omega
  have hr : 1000 ≤ R := by omega
  have hm : R / 256 ≤ R := Nat.div_le_self _ _
  have hs : R / 256 * (R + 3) + (R / 256 + R + 1) ≤ 2 * R ^ 2 := by
    have h := Nat.mul_le_mul_right (R + 3) hm
    nlinarith
  have ht : 20 * (R + 1) * (2 * R ^ 2) ≤ R ^ 4 := by
    have h : 40 * (R + 1) ≤ R ^ 2 := by nlinarith
    have hd := Nat.mul_le_mul_right (R ^ 2) h
    nlinarith only [hd]
  have heu : (R / 256 * (R + 3)) * u + (R / 256 + R + 1) ≤ 2 * R ^ 2 * u := by
    calc
      _ ≤ (R / 256 * (R + 3)) * u + (R / 256 + R + 1) * u :=
        Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left (R / 256 + R + 1) hu) _
      _ = (R / 256 * (R + 3) + (R / 256 + R + 1)) * u := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hs
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  unfold cssXDimension
  calc
    _ ≤ (2 * R ^ 2 * u) * (20 * (R + 1)) := Nat.mul_le_mul_right _ heu
    _ = 20 * (R + 1) * (2 * R ^ 2) * u := by ring
    _ ≤ _ := by simpa [mul_comm] using Nat.mul_le_mul_right u ht

theorem css_linear_global_slack (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    cssXDimension R * cssXDimension R + cssXDimension R + R / 256 + R ≤ cssSites R / 2 := by
  have hp : 0 < R := by omega
  have hr : 4 ≤ R := by omega
  have h48 : R ^ 4 ≤ R ^ 8 := Nat.pow_le_pow_right hp (by decide)
  have hd8 : R ≤ R ^ 8 := by simpa using Nat.pow_le_pow_right hp (by decide : 1 ≤ 8)
  have hN : 8 * R ^ 8 ≤ R ^ 12 := by
    have h4' : 8 ≤ R ^ 4 := (show 8 ≤ 4 ^ 4 by decide).trans (Nat.pow_le_pow_left hr _)
    rw [show (12 : ℕ) = 4 + 8 by decide, pow_add]
    exact Nat.mul_le_mul_right _ h4'
  have hdiv : R / 256 ≤ R := Nat.div_le_self _ _
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  unfold cssXDimension cssSites
  rw [show R ^ 4 * R ^ 4 = R ^ 8 by ring]
  omega

end CriticalDepth.Manuscript20261114.CSSCheckSpaces