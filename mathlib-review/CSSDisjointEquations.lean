import CSSCheckSpaces

/-!
# Counting disjoint dependence sets

The sparse automorphism argument samples independent row equations on
disjoint coordinate sets. A greedy maximal disjoint family gives a lower
bound for the number of such equations.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

theorem exists_disjoint_family_card_bound (rows : Finset ι) (dependencies : ι → Finset α)
    (width occurrence : ℕ)
    (hne : ∀ i ∈ rows, (dependencies i).Nonempty)
    (hwidth : ∀ i ∈ rows, (dependencies i).card ≤ width)
    (hocc : ∀ a : α, (rows.filter fun i => a ∈ dependencies i).card ≤ occurrence) :
    ∃ independent ⊆ rows, (independent : Set ι).PairwiseDisjoint dependencies ∧
      rows.card ≤ independent.card * (width * occurrence) := by
  classical
  let candidates := rows.powerset.filter fun s : Finset ι => (s : Set ι).PairwiseDisjoint dependencies
  have hsmall : (∅ : Finset ι) ∈ candidates := by simp [candidates, Set.PairwiseDisjoint, Set.Pairwise]
  obtain ⟨S, hSc, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, hsmall⟩
  obtain ⟨hsubs, hdis⟩ := Finset.mem_filter.mp hSc
  have hS : S ⊆ rows := Finset.mem_powerset.mp hsubs
  have hcover (i : ι) (hi : i ∈ rows) :
      ∃ j ∈ S, (dependencies i ∩ dependencies j).Nonempty := by
    by_cases hsi : i ∈ S
    · exact ⟨i, hsi, by simpa using hne i hi⟩
    by_contra! hn
    have hpair : ((insert i S : Finset ι) : Set ι).PairwiseDisjoint dependencies := by
      intro j hj k hk hjk
      change j ∈ insert i S at hj
      change k ∈ insert i S at hk
      by_cases hij : j = i
      · subst j
        have hk' : k ∈ S := (Finset.mem_insert.mp hk).resolve_left hjk.symm
        exact Finset.disjoint_iff_inter_eq_empty.mpr (hn k hk')
      · have hj' : j ∈ S := (Finset.mem_insert.mp hj).resolve_left hij
        by_cases hik : k = i
        · subst k
          exact (Finset.disjoint_iff_inter_eq_empty.mpr (hn j hj')).symm
        · have hk' : k ∈ S := (Finset.mem_insert.mp hk).resolve_left hik
          exact hdis hj' hk' hjk
    have hmem : insert i S ∈ candidates :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hS), hpair⟩
    have hle := hmax (insert i S) hmem
    rw [Finset.card_insert_of_notMem hsi] at hle
    omega
  let neighborhood (j : ι) := (dependencies j).biUnion fun a => rows.filter fun i => a ∈ dependencies i
  have hsub : rows ⊆ S.biUnion neighborhood := by
    intro i hi
    obtain ⟨j, hj, a, ha⟩ := hcover i hi
    obtain ⟨hai, haj⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_biUnion.mpr ⟨a, haj, Finset.mem_filter.mpr ⟨hi, hai⟩⟩⟩
  have hneighbors (j : ι) (hj : j ∈ S) : (neighborhood j).card ≤ width * occurrence := by
    calc
      _ ≤ ∑ a ∈ dependencies j, (rows.filter fun i => a ∈ dependencies i).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ dependencies j, occurrence := Finset.sum_le_sum fun a _ => hocc a
      _ = (dependencies j).card * occurrence := by simp
      _ ≤ width * occurrence := Nat.mul_le_mul_right _ (hwidth j (hS hj))
  refine ⟨S, hS, hdis, ?_⟩
  calc
    rows.card ≤ (S.biUnion neighborhood).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ S, (neighborhood j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ S, width * occurrence := Finset.sum_le_sum hneighbors
    _ = S.card * (width * occurrence) := by simp

#print axioms exists_disjoint_family_card_bound

end CriticalDepth.Manuscript20261114.CSSCheckSpaces