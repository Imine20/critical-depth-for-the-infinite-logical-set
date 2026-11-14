import CSSSparseLinearIntertwiner
import CSSRandomScale
import CSSSparseMatrixCounts

/-!
Combining the independent row bounds for the sparse linear exclusion.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators Matrix

local notation "𝔽" => ZMod 2
variable {n a : ℕ}

theorem sparse_linear_fixed_count_scaled
    (F : Matrix (Fin n) (Fin n) 𝔽) (S : Matrix (Fin a) (Fin a) 𝔽) (R B : ℕ)
    (hF : Function.Surjective F.mulVec) (hS : S ≠ 1)
    (hrow : ∀ i, wordWeight (F.row i) ≤ R) (hcol : ∀ j, wordWeight (fun i => F i j) ≤ R)
    (hB : ((R + 1) * (R + 1)) * (2 * B + 1) ≤ a) :
    (Finset.univ.filter fun A : Matrix (Fin n) (Fin a) 𝔽 => F * A = A * S).card *
        2 ^ (n / 2 + (changedRows F).card * B) ≤ 2 ^ (a * n) := by
  obtain ⟨k, hk, hu, hchg⟩ := card_sparse_automorphism_changed_bound F S R hF hrow hcol
  have hunch := card_sparse_automorphism_unchanged_bound F S hS
  let u := (changedRows F).card
  have hUn : u ≤ n := by simpa [u] using Finset.card_le_univ (changedRows F)
  have hu' : u * (2 * B + 1) ≤ a * k := calc
    _ ≤ (k * ((R + 1) * (R + 1))) * (2 * B + 1) := Nat.mul_le_mul_right _ hu
    _ = k * (((R + 1) * (R + 1)) * (2 * B + 1)) := by ring
    _ ≤ k * a := Nat.mul_le_mul_left _ hB
    _ = a * k := Nat.mul_comm _ _
  have heq : u * (2 * B + 1) = 2 * (u * B) + u := by ring
  rw [heq] at hu'
  have hbig : n / 2 + u * B ≤ max (n - u) (a * k) := by
    have h1 := le_max_left (n - u) (a * k)
    have h2 := le_max_right (n - u) (a * k)
    omega
  let d := n / 2 + u * B
  have hfull : a * (n - k) + a * k = a * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk]
  by_cases hd : d ≤ a * k
  · exact (Nat.mul_le_mul_right _ hchg).trans (by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      change a * (n - k) + d ≤ a * n
      rw [← hfull]
      exact Nat.add_le_add_left hd _)
  · have hd' : d ≤ n - u := by
      exact (le_max_iff.mp hbig).resolve_right hd
    have hna : n - u ≤ a * n := by
      have ha : 1 ≤ a := by
        have hpos : 0 < ((R + 1) * (R + 1)) * (2 * B + 1) := by positivity
        omega
      exact (Nat.sub_le _ _).trans (by simpa using Nat.mul_le_mul_right n ha)
    exact (Nat.mul_le_mul_right _ hunch).trans (by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      change a * n - (n - u) + d ≤ a * n
      omega)

theorem css_sparse_linear_coefficient_budget (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    ((R + 1) * (R + 1)) * (2 * (R ^ 2 / 16) + 1) ≤ cssXDimension R ∧
      (R / 256) * (R + 2) ≤ R ^ 2 / 16 := by
  have hr : 4 ≤ R := by omega
  have hR2 : 16 ≤ R ^ 2 := by nlinarith
  have hA : (R + 1) * (R + 1) ≤ 2 * R ^ 2 := by nlinarith
  have hf : 4 * (2 * (R ^ 2 / 16) + 1) ≤ R ^ 2 := by omega
  have hb : 2 * (2 * (R ^ 2 / 16) + 1) ≤ R ^ 2 := by omega
  constructor
  · unfold cssXDimension
    calc
      _ ≤ (2 * R ^ 2) * (2 * (R ^ 2 / 16) + 1) := Nat.mul_le_mul_right _ hA
      _ = R ^ 2 * (2 * (2 * (R ^ 2 / 16) + 1)) := by ring
      _ ≤ R ^ 2 * R ^ 2 := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  · have hd : (R / 256) * 256 ≤ R := Nat.div_mul_le_self _ _
    have he : 16 * ((R / 256) * (R + 2)) ≤ R ^ 2 := calc
      _ = (R / 256) * (16 * (R + 2)) := by ring
      _ ≤ (R / 256) * (256 * R) := Nat.mul_le_mul_left _ (by omega)
      _ = ((R / 256) * 256) * R := by ring
      _ ≤ R ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul_right R hd
    exact (Nat.le_div_iff_mul_le (by decide)).mpr (by simpa only [mul_comm] using he)

#print axioms sparse_linear_fixed_count_scaled
#print axioms css_sparse_linear_coefficient_budget

end CriticalDepth.Manuscript20261114.CSSCheckSpaces