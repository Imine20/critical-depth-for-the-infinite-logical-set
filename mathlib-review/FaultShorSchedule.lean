import FaultShorSaturation
import Mathlib.Data.Fintype.EquivFin

/-!
# Packing and mask transformations for the Shor saturation circuit

The intermediate layers expand one marked mask while compressing the
other. All operations are on existing sites in a cell. A fanout layer
uses disjoint groups of targets whose pivots are unchanged.
-/

namespace CriticalDepth.FaultShorSaturation

def cellSize (q h : ℕ) : ℕ := q ^ (h - 1) + 1

theorem groupSize_eq_cells (q h : ℕ) (hh : 1 ≤ h) :
    q ^ h + q = q * cellSize q h := by
  rw [cellSize, Nat.mul_add, mul_one, mul_comm q (q ^ (h - 1)), ← pow_succ]
  rw [show h - 1 + 1 = h by omega]

/-- Sufficient free space for the intermediate A-expansion and D-compression. -/
theorem intermediate_support_budget (q h j : ℕ)
    (hq : 2 ≤ q) (hj : 2 ≤ j) (hjh : j < h) :
    q ^ (j - 1) + q ^ (h - j) ≤ q ^ (h - 1) := by
  have hqa : q ^ (j - 1) ≤ q ^ (h - 2) :=
    pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
  have hqd : q ^ (h - j) ≤ q ^ (h - 2) :=
    pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
  calc
    _ ≤ q ^ (h - 2) + q ^ (h - 2) := Nat.add_le_add hqa hqd
    _ = q ^ (h - 2) * 2 := by omega
    _ ≤ q ^ (h - 2) * q := Nat.mul_le_mul_left _ hq
    _ = _ := by rw [← pow_succ, show h - 2 + 1 = h - 1 by omega]

/-- The first compression is integral: every supported block has size q. -/
theorem first_compression_count (q h : ℕ) (hh : 2 ≤ h) :
    q ^ (h - 1) = q ^ (h - 2) * q := by
  rw [← pow_succ, show h - 2 + 1 = h - 1 by omega]

theorem intermediate_expansion_count (q j : ℕ) (hj : 2 ≤ j) :
    q ^ (j - 1) = q ^ (j - 2) * q := by
  rw [← pow_succ, show j - 2 + 1 = j - 1 by omega]

theorem intermediate_compression_count (q h j : ℕ) (hjh : j < h) :
    q ^ (h - j) = q ^ (h - j - 1) * q := by
  rw [← pow_succ, show h - j - 1 + 1 = h - j by omega]

/-- Enlarge A to the prescribed cardinality without touching D. -/
theorem exists_disjoint_enlargement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Finset ι) (hAD : Disjoint A D) (a : ℕ)
    (hA : A.card ≤ a) (hbudget : a + D.card ≤ Fintype.card ι) :
    ∃ A' : Finset ι, A ⊆ A' ∧ Disjoint A' D ∧ A'.card = a := by
  classical
  let free := Finset.univ \ (A ∪ D)
  have hfree : free.card = Fintype.card ι - (A ∪ D).card := by
    exact Finset.card_sdiff_of_subset (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hAD] at hfree
  obtain ⟨B, hB, hcard⟩ := Finset.exists_subset_card_eq
    (show a - A.card ≤ free.card by omega)
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp (hB hiB)).2 (Finset.mem_union_left _ hiA)
  have hBD : Disjoint B D := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiB hiD
    exact (Finset.mem_sdiff.mp (hB hiB)).2 (Finset.mem_union_right _ hiD)
  refine ⟨A ∪ B, Finset.subset_union_left, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun i hi hiD =>
      (Finset.mem_union.mp hi).elim
        (fun hiA => Finset.disjoint_left.mp hAD hiA hiD)
        (fun hiB => Finset.disjoint_left.mp hBD hiB hiD)
  · rw [Finset.card_union_of_disjoint hAB, hcard]
    omega

/-- In a cell, choose nested supports for the two intermediate changes. -/
theorem exists_intermediate_support_step (q h j : ℕ)
    (hq : 2 ≤ q) (hj : 2 ≤ j) (hjh : j < h)
    (A D : Finset (Fin (cellSize q h))) (hAD : Disjoint A D)
    (hA : A.card = q ^ (j - 2)) (hD : D.card = q ^ (h - j)) :
    ∃ A' D' : Finset (Fin (cellSize q h)),
      A ⊆ A' ∧ D' ⊆ D ∧ Disjoint A' D ∧
      A'.card = q ^ (j - 1) ∧ D'.card = q ^ (h - j - 1) := by
  have hA' : A.card ≤ q ^ (j - 1) := by
    rw [hA]
    exact pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
  have hbudget : q ^ (j - 1) + D.card ≤ Fintype.card (Fin (cellSize q h)) := by
    rw [hD, Fintype.card_fin, cellSize]
    exact (intermediate_support_budget q h j hq hj hjh).trans (by omega)
  obtain ⟨A', hAA', hA'D, hA'⟩ :=
    exists_disjoint_enlargement A D hAD _ hA' hbudget
  have hD' : q ^ (h - j - 1) ≤ D.card := by
    rw [hD]
    exact pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
  obtain ⟨D', hD'D, hD'⟩ := Finset.exists_subset_card_eq hD'
  exact ⟨A', D', hAA', hD'D, hA'D, hA', hD'⟩

/-- A single simultaneous fanout: each target adds the value of its pivot.
The pivot condition forbids a pivot from itself being a target. -/
def fanout {ι : Type*} (parent : ι → Option ι) (x : ι → Bit) (i : ι) : Bit :=
  match parent i with
  | none => x i
  | some a => x i + x a

private theorem add_self_bit (x : Bit) : x + x = 0 := by
  have ht : (2 : Bit) = 0 := by decide
  rw [← two_mul, ht, zero_mul]

theorem fanout_involutive {ι : Type*} (parent : ι → Option ι)
    (pivotUntouched : ∀ i a, parent i = some a → parent a = none) :
    Function.Involutive (fanout parent) := by
  intro x
  funext i
  cases h : parent i with
  | none => simp [fanout, h]
  | some a =>
    have ha := pivotUntouched i a h
    simp [fanout, h, ha, add_assoc, add_self_bit]

/-- Invertible binary map realized by the controlled additions of one layer. -/
def fanoutLinearEquiv {ι : Type*} (parent : ι → Option ι)
    (pivotUntouched : ∀ i a, parent i = some a → parent a = none) :
    (ι → Bit) ≃ₗ[Bit] (ι → Bit) where
  toFun := fanout parent
  invFun := fanout parent
  left_inv := fanout_involutive parent pivotUntouched
  right_inv := fanout_involutive parent pivotUntouched
  map_add' := by
    intro x y
    funext i
    cases h : parent i <;> simp [fanout, h, Pi.add_apply] <;> abel
  map_smul' := by
    intro r x
    funext i
    cases h : parent i <;> simp [fanout, h, Pi.smul_apply, mul_add]


/-- Membership mask taking values zero and one in the binary field. -/
def mark {ι : Type*} [DecidableEq ι] (A : Finset ι) : ι → Bit :=
  fun i => if i ∈ A then 1 else 0

/-- Toggle exactly the added A sites and the removed D sites. Every pivot
lies in an untouched part, so all controlled additions are simultaneous. -/
noncomputable def transitionParent {ι : Type*} [DecidableEq ι]
    (A A' D D' : Finset ι) (q : ℕ)
    (eA : (A' \ A : Finset ι) ≃ A × Fin (q - 1))
    (eD : (D \ D' : Finset ι) ≃ D' × Fin (q - 1)) (i : ι) : Option ι :=
  if hi : i ∈ A' \ A then some (eA ⟨i, hi⟩).1.val
  else if hi' : i ∈ D \ D' then some (eD ⟨i, hi'⟩).1.val else none

private theorem transitionParent_never_targets_pivot {ι : Type*} [DecidableEq ι]
    (A A' D D' : Finset ι) (q : ℕ)
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (eA : (A' \ A : Finset ι) ≃ A × Fin (q - 1))
    (eD : (D \ D' : Finset ι) ≃ D' × Fin (q - 1)) :
    ∀ i a, transitionParent A A' D D' q eA eD i = some a →
      transitionParent A A' D D' q eA eD a = none := by
  classical
  have hnoneA (a : ι) (ha : a ∈ A) :
      transitionParent A A' D D' q eA eD a = none := by
    have hnotD : a ∉ D := fun hd => Finset.disjoint_left.mp hA'D (hAA' ha) hd
    simp [transitionParent, ha, hnotD]
  have hnoneD (a : ι) (ha : a ∈ D') :
      transitionParent A A' D D' q eA eD a = none := by
    have hnotA : a ∉ A' := fun h => Finset.disjoint_left.mp hA'D h (hD'D ha)
    simp [transitionParent, ha, hnotA]
  intro i a hp
  by_cases hi : i ∈ A' \ A
  · have he : (eA ⟨i, hi⟩).1.val = a := by simpa [transitionParent, hi] using hp
    exact he ▸ hnoneA _ (eA ⟨i, hi⟩).1.property
  · by_cases hi' : i ∈ D \ D'
    · have he : (eD ⟨i, hi'⟩).1.val = a := by simpa [transitionParent, hi, hi'] using hp
      exact he ▸ hnoneD _ (eD ⟨i, hi'⟩).1.property
    · simp [transitionParent, hi, hi'] at hp

private theorem transition_fanout_expands_A {ι : Type*} [DecidableEq ι]
    (A A' D D' : Finset ι) (q : ℕ)
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (eA : (A' \ A : Finset ι) ≃ A × Fin (q - 1))
    (eD : (D \ D' : Finset ι) ≃ D' × Fin (q - 1)) :
    fanout (transitionParent A A' D D' q eA eD) (mark A) = mark A' := by
  classical
  funext i
  by_cases hi : i ∈ A' \ A
  · have hmem := Finset.mem_sdiff.mp hi
    exact show fanout (transitionParent A A' D D' q eA eD) (mark A) i = mark A' i by
      simp [fanout, transitionParent, hi, mark, hmem.1, hmem.2, (eA ⟨i, hi⟩).1.property]
  · by_cases hi' : i ∈ D \ D'
    · have hpD : (eD ⟨i, hi'⟩).1.val ∈ D := hD'D (eD ⟨i, hi'⟩).1.property
      have hpA : (eD ⟨i, hi'⟩).1.val ∉ A :=
        fun h => Finset.disjoint_left.mp hA'D (hAA' h) hpD
      have hnotA' : i ∉ A' := fun h => Finset.disjoint_left.mp hA'D h (Finset.mem_sdiff.mp hi').1
      have hnotA : i ∉ A := fun h => hnotA' (hAA' h)
      simp [fanout, transitionParent, hi, hi', mark, hnotA', hnotA, hpA]
    · have hm : i ∈ A ↔ i ∈ A' :=
        ⟨fun ha => hAA' ha, fun ha' => by
          by_contra hn
          exact hi (Finset.mem_sdiff.mpr ⟨ha', hn⟩)⟩
      simp [fanout, transitionParent, hi, hi', mark, hm]

private theorem transition_fanout_compresses_D {ι : Type*} [DecidableEq ι]
    (A A' D D' : Finset ι) (q : ℕ)
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (eA : (A' \ A : Finset ι) ≃ A × Fin (q - 1))
    (eD : (D \ D' : Finset ι) ≃ D' × Fin (q - 1)) :
    fanout (transitionParent A A' D D' q eA eD) (mark D) = mark D' := by
  classical
  funext i
  by_cases hi : i ∈ A' \ A
  · have hnotD : i ∉ D := Finset.disjoint_left.mp hA'D (Finset.mem_sdiff.mp hi).1
    have hnotD' : i ∉ D' := fun hd => hnotD (hD'D hd)
    have hpD : (eA ⟨i, hi⟩).1.val ∉ D :=
      Finset.disjoint_left.mp hA'D (hAA' (eA ⟨i, hi⟩).1.property)
    simp [fanout, transitionParent, hi, mark, hnotD, hnotD', hpD]
  · by_cases hi' : i ∈ D \ D'
    · have hpD : (eD ⟨i, hi'⟩).1.val ∈ D := hD'D (eD ⟨i, hi'⟩).1.property
      have hmem := Finset.mem_sdiff.mp hi'
      simp [fanout, transitionParent, hi, hi', mark, hmem.1, hmem.2, hpD, add_self_bit]
    · have hm : i ∈ D ↔ i ∈ D' :=
        ⟨fun hd => by by_contra hnd; exact hi' (Finset.mem_sdiff.mpr ⟨hd, hnd⟩),
          fun hd => hD'D hd⟩
      simp [fanout, transitionParent, hi, hi', mark, hm]

private theorem transitionCard (q : ℕ) (hq : 1 ≤ q) (m : ℕ) :
    m * q - m = m * (q - 1) := by rw [Nat.mul_sub, mul_one]

/-- The two compatible support transitions are implemented by one reversible
binary fanout layer. Each displayed equivalence assigns exactly q−1 targets
to each pivot in its sector. The two target lists and all pivots are disjoint. -/
theorem exists_fanout_transition {ι : Type*} [DecidableEq ι]
    (q : ℕ) (hq : 1 ≤ q) (A A' D D' : Finset ι)
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (hA' : A'.card = A.card * q) (hD : D.card = D'.card * q) :
    ∃ (eA : (A' \ A : Finset ι) ≃ A × Fin (q - 1))
      (eD : (D \ D' : Finset ι) ≃ D' × Fin (q - 1))
      (hun : ∀ i a, transitionParent A A' D D' q eA eD i = some a →
        transitionParent A A' D D' q eA eD a = none),
      fanoutLinearEquiv (transitionParent A A' D D' q eA eD) hun (mark A) = mark A' ∧
      fanoutLinearEquiv (transitionParent A A' D D' q eA eD) hun (mark D) = mark D' := by
  classical
  let eA : (A' \ A : Finset ι) ≃ A × Fin (q - 1) := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin,
      Finset.card_sdiff_of_subset hAA', hA', transitionCard q hq])
  let eD : (D \ D' : Finset ι) ≃ D' × Fin (q - 1) := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin,
      Finset.card_sdiff_of_subset hD'D, hD, transitionCard q hq])
  refine ⟨eA, eD, transitionParent_never_targets_pivot A A' D D' q hAA' hD'D hA'D eA eD, ?_, ?_⟩
  · exact transition_fanout_expands_A A A' D D' q hAA' hD'D hA'D eA eD
  · exact transition_fanout_compresses_D A A' D D' q hAA' hD'D hA'D eA eD

#print axioms exists_fanout_transition

/-- The two disjoint masks of a partition add to the all-ones mask. -/
theorem mark_partition_add_eq_one {ι : Type*} [DecidableEq ι]
    (A D : Finset ι) (hAD : Disjoint A D)
    (hcover : ∀ i : ι, i ∈ A ∪ D) : mark A + mark D = 1 := by
  funext i
  rcases Finset.mem_union.mp (hcover i) with hi | hi
  · have hnot : i ∉ D := Finset.disjoint_left.mp hAD hi
    simp [mark, hi, hnot]
  · have hnot : i ∉ A := fun ha => Finset.disjoint_left.mp hAD ha hi
    simp [mark, hi, hnot]

/-- A row transformer carrying complementary marked masks to complementary
marked masks preserves the all-ones vector. -/
theorem fixes_one_of_marked_partitions {ι : Type*} [DecidableEq ι]
    (T : (ι → Bit) →ₗ[Bit] (ι → Bit))
    (A D A' D' : Finset ι) (hAD : Disjoint A D) (hA'D' : Disjoint A' D')
    (hcover : ∀ i : ι, i ∈ A ∪ D) (hcover' : ∀ i : ι, i ∈ A' ∪ D')
    (hA : T (mark A) = mark A') (hD : T (mark D) = mark D') : T 1 = 1 := by
  calc
    T 1 = T (mark A + mark D) := congrArg T (mark_partition_add_eq_one A D hAD hcover).symm
    _ = mark A' + mark D' := by rw [map_add, hA, hD]
    _ = 1 := mark_partition_add_eq_one A' D' hA'D' hcover'

/-- The cell transition has exact cardinalities and a single binary layer
of width at most q, given by assigning q−1 target sites to each pivot. -/
theorem exists_intermediate_fanout_step (q h j : ℕ)
    (hq : 2 ≤ q) (hj : 2 ≤ j) (hjh : j < h)
    (A D : Finset (Fin (cellSize q h))) (hAD : Disjoint A D)
    (hA : A.card = q ^ (j - 2)) (hD : D.card = q ^ (h - j)) :
    ∃ (A' D' : Finset (Fin (cellSize q h))),
      A'.card = q ^ (j - 1) ∧ D'.card = q ^ (h - j - 1) ∧
      Disjoint A' D' ∧
      ∃ (eA : (A' \ A : Finset _) ≃ A × Fin (q - 1))
        (eD : (D \ D' : Finset _) ≃ D' × Fin (q - 1))
        (hun : ∀ i a, transitionParent A A' D D' q eA eD i = some a →
          transitionParent A A' D D' q eA eD a = none),
        fanoutLinearEquiv (transitionParent A A' D D' q eA eD) hun (mark A) = mark A' ∧
        fanoutLinearEquiv (transitionParent A A' D D' q eA eD) hun (mark D) = mark D' := by
  obtain ⟨A', D', hAA', hD'D, hA'D, hAc, hDc⟩ :=
    exists_intermediate_support_step q h j hq hj hjh A D hAD hA hD
  refine ⟨A', D', hAc, hDc, hA'D.mono_right hD'D, ?_⟩
  apply exists_fanout_transition q (by omega) A A' D D' hAA' hD'D hA'D
  · rw [hAc, hA, intermediate_expansion_count q j hj]
  · rw [hD, hDc, intermediate_compression_count q h j hjh]

#print axioms fixes_one_of_marked_partitions
#print axioms exists_intermediate_fanout_step
#print axioms groupSize_eq_cells
#print axioms intermediate_support_budget
#print axioms exists_intermediate_support_step
#print axioms fanout_involutive

end CriticalDepth.FaultShorSaturation
