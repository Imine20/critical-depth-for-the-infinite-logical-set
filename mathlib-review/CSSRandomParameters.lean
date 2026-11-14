import CSSRigidityCheckSpaces

/-!
Parameters of the CSS family and finite inequalities used in the
existence and final distance proofs.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

def cssSites (R : ℕ) : ℕ := R ^ 12
def cssDistance (R : ℕ) : ℕ := R ^ 2
def cssXDimension (R : ℕ) : ℕ := R ^ 4
def cssZDimension (R : ℕ) : ℕ := R ^ 6

def cssDeletionThreshold (R : ℕ) : ℕ :=
  max (R * (cssXDimension R + 1)) ((cssZDimension R + 1) * (R + 1) + R)

theorem cssDistance_le_supportBound (R : ℕ) (hR : 1 ≤ R) :
    cssDistance R ≤ R * (cssXDimension R + 1) := by
  have h := Nat.pow_le_pow_right (by omega : 0 < R) (by decide : 1 ≤ 4)
  simp only [pow_one] at h
  change R ^ 2 ≤ R * (R ^ 4 + 1)
  rw [pow_two]
  exact Nat.mul_le_mul_left _ (h.trans (Nat.le_add_right _ _))

theorem cssDistance_le_deletionThreshold (R : ℕ) (hR : 1 ≤ R) :
    cssDistance R ≤ cssDeletionThreshold R :=
  (cssDistance_le_supportBound R hR).trans (le_max_left _ _)

theorem cssDistance_gt_localBound (R : ℕ) (hR : 2 ≤ R) :
    R + 1 < cssDistance R := by
  change R + 1 < R ^ 2
  nlinarith

theorem cssXDimension_le_sites (R : ℕ) (hR : 1 ≤ R) : 1 ≤ cssXDimension R := by
  unfold cssXDimension
  exact pow_pos (by omega : 0 < R) 4

theorem css_logicalDimension_positive (R : ℕ) (hR : 2 ≤ R) :
    cssXDimension R + cssZDimension R < cssSites R := by
  have hre : 0 < R := by omega
  have hpow : R ^ 4 ≤ R ^ 6 := Nat.pow_le_pow_right hre (by decide)
  have htwo : 2 < R ^ 6 := by
    have h : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right hre (by decide)
    have hh : 2 < R ^ 2 := by nlinarith
    exact hh.trans_le h
  change R ^ 4 + R ^ 6 < R ^ 12
  rw [show (12 : ℕ) = 6 + 6 by decide, pow_add]
  have h := Nat.mul_lt_mul_of_pos_right htwo (pow_pos hre 6)
  omega

theorem cssDeletionThreshold_le_four_mul_pow (R : ℕ) (hR : 2 ≤ R) :
    cssDeletionThreshold R ≤ 4 * R ^ 7 := by
  have hp : 0 < R := by omega
  have h47 : R ^ 4 ≤ R ^ 6 := Nat.pow_le_pow_right hp (by decide)
  have h17 : R ≤ R ^ 7 := by simpa using Nat.pow_le_pow_right hp (by decide : 1 ≤ 7)
  have hh : R ^ 4 + 1 ≤ 2 * R ^ 6 := by
    have h1 : 1 ≤ R ^ 6 := pow_pos hp _
    omega
  have hL : R * (R ^ 4 + 1) ≤ 2 * R ^ 7 := by
    calc
      _ ≤ R * (2 * R ^ 6) := Nat.mul_le_mul_left _ hh
      _ = 2 * R ^ 7 := by rw [pow_succ]; ring
  have hR' : (R ^ 6 + 1) * (R + 1) + R ≤ 4 * R ^ 7 := by
    have h1 : 1 ≤ R ^ 6 := pow_pos hp _
    have h6 : R ^ 6 ≤ R ^ 7 := Nat.pow_le_pow_right hp (by decide)
    have h2 : R + 1 ≤ R ^ 7 := by
      have hs : R + 1 ≤ R ^ 2 := by nlinarith
      exact hs.trans (Nat.pow_le_pow_right hp (by decide))
    rw [add_mul, one_mul, mul_add, mul_one, ← pow_succ]
    change R ^ 7 + R ^ 6 + (R + 1) + R ≤ 4 * R ^ 7
    omega
  unfold cssDeletionThreshold cssXDimension cssZDimension
  exact max_le (hL.trans (by omega)) hR'

#print axioms cssDistance_gt_localBound
#print axioms css_logicalDimension_positive
#print axioms cssDeletionThreshold_le_four_mul_pow

end CriticalDepth.Manuscript20261114.CSSCheckSpaces