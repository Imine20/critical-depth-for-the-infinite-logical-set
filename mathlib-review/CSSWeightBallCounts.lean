import CSSBadWordCounts
import CSSRandomParameters

/-!
# Good planted X checks from explicit finite inequalities

This theorem establishes the full-rank, primal-distance, and exact
dual-distance requirements. The two separate sparse exclusion arguments
are additional restrictions on the same finite sampling construction.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

def natShells (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), n.choose j

theorem card_binary_atMost_le (n k : ℕ) :
    (Finset.univ.filter fun x : BW n => wordWeight x ≤ k).card ≤ natShells n k := by
  classical
  let s := Finset.univ.filter fun x : BW n => wordWeight x ≤ k
  have hf (x : BW n) (hx : x ∈ s) : wordWeight x ∈ Finset.range (k + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.mem_filter.mp hx).2))
  rw [show (Finset.univ.filter fun x : BW n => wordWeight x ≤ k) = s from rfl,
    Finset.card_eq_sum_card_fiberwise hf]
  unfold natShells
  apply Finset.sum_le_sum
  intro j hj
  let t := s.filter fun x => wordWeight x = j
  have hs : t ⊆ Finset.univ.filter fun x : BW n => wordWeight x = j :=
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  apply (Finset.card_le_card hs).trans
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hWeight (x : BW n) : wordWeight x = (wordSupport x).card := by
    unfold wordWeight wordSupport
    have h (d₁ d₂ : DecidablePred (fun i : Fin n => x i ≠ 0)) :
        @Finset.filter (Fin n) (fun i => x i ≠ 0) d₁ Finset.univ =
        @Finset.filter (Fin n) (fun i => x i ≠ 0) d₂ Finset.univ :=
      @Finset.filter_congr_decidable _ _ (fun i : Fin n => x i ≠ 0) d₁ d₂
    exact congrArg Finset.card (h _ _)
  simpa only [← hWeight] using card_binary_weight_shell_le n j

end CriticalDepth.Manuscript20261114.CSSCheckSpaces