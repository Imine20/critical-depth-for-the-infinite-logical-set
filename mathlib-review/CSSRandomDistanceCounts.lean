import CSSRandomShellScale
import CSSRandomXChecks
import CSSRandomZChecks

/-!
The distance and full-rank bad events have uniformly small finite counts
at the manuscript's parameters.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode

theorem css_planted_card_distance_bad (R : ℕ) (hR : 2 ^ 20 ≤ R)
    (p : BW (cssSites R)) (hp : p ≠ 0) :
    Nat.card {G : Fin (cssXDimension R) → PlantedColumnSpace p //
      badXCheckSample p (cssDistance R) (R * (cssXDimension R + 1)) G} * 2 ^ R ≤
        Nat.card (Fin (cssXDimension R) → PlantedColumnSpace p) := by
  let a := cssXDimension R
  let n := cssSites R
  let d := cssDistance R
  let w := R * (a + 1)
  let k := (R / 256) * (w + 1)
  letI : Fintype (PlantedColumnSpace p) := Fintype.ofFinite _
  let N := Fintype.card (PlantedColumnSpace p)
  have hN : N = 2 ^ (n - 1) := by
    rw [show N = Nat.card (PlantedColumnSpace p) from Nat.card_eq_fintype_card.symm]
    exact card_planted_columnSpace p hp
  have hRpos : 0 < R := by omega
  have ha : 0 < a := by dsimp [a, cssXDimension]; positivity
  have hscale := css_x_check_scale R hR
  have m1 : k + a + (R + 1) ≤ n - 1 := by
    dsimp [k, a, n, w]
    omega
  have hw : w + 1 ≤ n := by
    have hr : 1 ≤ R / 256 := by omega
    have h := Nat.mul_le_mul_right (w + 1) hr
    dsimp [k] at m1
    omega
  have hds : d + 1 ≤ n := (Nat.succ_le_succ (cssDistance_le_supportBound R (by omega))).trans hw
  have hd8 : (R / 256) * (d + 1) + (R + 1) ≤ a := by
    dsimp [d, a]
    omega
  have hcD : natShells n d ≤ 2 ^ (a - (R + 1)) :=
    (css_bound_for_shells R d hR hds).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hcard := card_bad_xChecks_le (a := a) (d := d) (w := w) p
  rw [Nat.card_eq_fintype_card (α := (Fin a → PlantedColumnSpace p)),
    Fintype.card_fun, Fintype.card_fin]
  exact (Nat.mul_le_mul_right _ hcard).trans
    (binaryCheck_distance_bad_scaled a k R (natShells n w) (natShells n d) ha (css_bound_for_shells R w hR hw) hcD
      (by omega) N (hN ▸ Nat.pow_le_pow_right (by decide) m1))

theorem css_z_card_distance_bad (R : ℕ) (hR : 2 ^ 20 ≤ R)
    (H : Submodule CSSBit (BW (cssSites R))) (hH : Module.finrank CSSBit H = cssXDimension R)
    (hDist : ∀ x ∈ H, x ≠ 0 → R * (cssXDimension R + 1) < wordWeight x) :
    Nat.card {D : Fin (cssZDimension R) → cssOrthogonal H //
      badZCheckSample H (cssDeletionThreshold R) (R * (cssXDimension R + 1)) D} * 2 ^ R ≤
        Nat.card (Fin (cssZDimension R) → cssOrthogonal H) := by
  let n := cssSites R
  let b := cssZDimension R
  let T := cssDeletionThreshold R
  let W := R * (cssXDimension R + 1)
  let k := (R / 256) * (T + 1)
  letI : Fintype (cssOrthogonal H) := Fintype.ofFinite _
  let N := Fintype.card (cssOrthogonal H)
  have hN : N = 2 ^ (n - cssXDimension R) := by
    dsimp [N, n]
    rw [Module.card_eq_pow_finrank (K := CSSBit), ZMod.card, cssOrthogonal_finrank, hH]
  have hscale := css_z_check_scale R hR
  have hK : k + b + (R + 1) ≤ n - cssXDimension R := by
    dsimp [k, b, n, T]
    omega
  have hb : 0 < b := by dsimp [b, cssZDimension]; positivity
  have hT : T + 1 ≤ n := by
    have hr : 1 ≤ R / 256 := by omega
    have h := Nat.mul_le_mul_right (T + 1) hr
    dsimp [k] at hK
    omega
  have hw : W + 1 ≤ n := (Nat.succ_le_succ (le_max_left _ _)).trans hT
  have hd8 : (R / 256) * (W + 1) + (R + 1) ≤ b := by
    dsimp [W, b]
    omega
  have hcW : natShells n W ≤ 2 ^ (b - (R + 1)) :=
    (css_bound_for_shells R W hR hw).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hcard := card_bad_zChecks_le H b T W hDist
  rw [Nat.card_eq_fintype_card (α := (Fin b → cssOrthogonal H)),
    Fintype.card_fun, Fintype.card_fin]
  exact (Nat.mul_le_mul_right _ hcard).trans
    (binaryCheck_distance_bad_scaled b k R (natShells n T) (natShells n W) hb (css_bound_for_shells R T hR hT) hcW
      (by omega) N (hN ▸ Nat.pow_le_pow_right (by decide) hK))

end CriticalDepth.Manuscript20261114.CSSCheckSpaces