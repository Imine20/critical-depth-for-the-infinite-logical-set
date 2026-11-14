import CSSColumnRankCounts

/-!
Counting the exceptional binary words in the planted construction.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem card_linearCombination_bad_le (y : ι → ZMod 2) (hy : y ≠ 0)
    (bad : Finset V) :
    Nat.card {A : ι → V // (∑ j, y j • A j) ∈ bad} ≤
      bad.card * (Fintype.card V) ^ (Fintype.card ι - 1) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! hn
    exact hy (funext hn)
  let f (A : ι → V) := ∑ j, y j • A j
  let S := Finset.univ.filter (fun A : ι → V => (∑ j, y j • A j) ∈ bad)
  have hmap : ∀ a ∈ S, f a ∈ bad :=
    fun a ha => (Finset.mem_filter.mp ha).2
  have he := Finset.card_eq_sum_card_fiberwise (f := f) (t := bad) hmap
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change S.card ≤ _
  rw [he]
  calc
    _ ≤ ∑ v ∈ bad, (Fintype.card V) ^ (Fintype.card ι - 1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hfiber :
          (S.filter fun A => f A = v) =
            Finset.univ.filter fun A : ι → V => f A = v := by
        ext A
        constructor
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
        · intro h
          have hh := (Finset.mem_filter.mp h).2
          have hm : f A ∈ bad := by rw [hh]; exact hv
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, hh⟩
      rw [hfiber, ← Fintype.card_subtype]
      rw [← Nat.card_eq_fintype_card]
      exact (card_linearCombination_fiber y i hi v).le
    _ = _ := by simp

#print axioms card_linearCombination_bad_le

end CriticalDepth.Manuscript20261114.CSSCheckSpaces