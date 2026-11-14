import FaultShorSchedule

/-!
# Iteration of the reversible Shor cell schedule

The first step compresses all sites except the seed. The middle steps
use the checked simultaneous fanout construction. The last step fills
the complement of the surviving D site. This records the binary maps
inside each cell. The two cross-cell cycle gates and their physical
Pauli fault locations are separate from this cell calculation.
-/

namespace CriticalDepth.FaultShorSaturation

abbrev Cell (q h : ℕ) := Fin (cellSize q h)
abbrev CellMap (q h : ℕ) := (Cell q h → Bit) ≃ₗ[Bit] (Cell q h → Bit)

def runCell {q h : ℕ} (steps : List (CellMap q h)) (v : Cell q h → Bit) :
    Cell q h → Bit :=
  steps.foldl (fun v T => T v) v

theorem runCell_append_step {q h : ℕ} (steps : List (CellMap q h))
    (T : CellMap q h) (v : Cell q h → Bit) :
    runCell (steps ++ [T]) v = T (runCell steps v) := by
  simp [runCell, List.foldl_append]

/-- Starting just after the first layer, run all requested intermediate
layers through layer j. -/
theorem exists_middle_cell_steps (q h j : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h)
    (hj : j ≤ h - 2) (A D : Finset (Cell q h)) (hAD : Disjoint A D)
    (hA : A.card = 1) (hD : D.card = q ^ (h - 2)) :
    ∃ (steps : List (CellMap q h)) (A' D' : Finset (Cell q h)),
      steps.length = j ∧ Disjoint A' D' ∧ A'.card = q ^ j ∧
      D'.card = q ^ (h - 2 - j) ∧
      runCell steps (mark A) = mark A' ∧ runCell steps (mark D) = mark D' := by
  induction j with
  | zero =>
    exact ⟨[], A, D, rfl, hAD, by simpa using hA, by simpa using hD, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨steps, A', D', hlen, hdis, hAc, hDc, hAV, hDV⟩ := ih (by omega)
    have hD' : D'.card = q ^ (h - (j + 2)) := by
      rw [hDc, show h - 2 - j = h - (j + 2) by omega]
    obtain ⟨A'', D'', hA'', hD'', hdis', eA, eD, hun, hX, hZ⟩ :=
      exists_intermediate_fanout_step q h (j + 2) hq (by omega) (by omega)
        A' D' hdis (by simpa using hAc) hD'
    let T : CellMap q h := fanoutLinearEquiv (transitionParent A' A'' D' D'' q eA eD) hun
    refine ⟨steps ++ [T], A'', D'', by simp [hlen], hdis',
      by simpa [show j + 2 - 1 = j + 1 by omega] using hA'',
      by simpa [show h - (j + 2) - 1 = h - 2 - (j + 1) by omega] using hD'',
      ?_, ?_⟩
    · rw [runCell_append_step, hAV]
      exact hX
    · rw [runCell_append_step, hDV]
      exact hZ

/-- A first-layer cell keeps its seed and compresses all other sites. -/
theorem exists_first_cell_step (q h : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h)
    (seed : Cell q h) :
    ∃ (T : CellMap q h) (D' : Finset (Cell q h)),
      Disjoint ({seed} : Finset (Cell q h)) D' ∧ D'.card = q ^ (h - 2) ∧
      T (mark {seed}) = mark {seed} ∧
      T (mark (Finset.univ.erase seed)) = mark D' := by
  classical
  let D : Finset (Cell q h) := Finset.univ.erase seed
  let A : Finset (Cell q h) := {seed}
  have hDA : Disjoint A D := by
    simp [A, D, Finset.disjoint_left]
  have hDc : D.card = q ^ (h - 1) := by
    simp [D, Finset.card_erase_of_mem, cellSize]
  have hbound : q ^ (h - 2) ≤ D.card := by
    rw [hDc]
    exact pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
  obtain ⟨D', hD', hD'c⟩ := Finset.exists_subset_card_eq hbound
  -- The seed is an idle wire for the within-cell layer. Represent compression
  -- with an empty A sector and prove preservation of the seed directly.
  obtain ⟨eA, eD, hun, _, hDmap⟩ :=
    exists_fanout_transition q (by omega) (∅ : Finset (Cell q h)) ∅ D D'
      (by simp) hD' (by simp) (by simp)
      (by rw [hDc, hD'c, first_compression_count q h hh])
  let T : CellMap q h := fanoutLinearEquiv (transitionParent ∅ ∅ D D' q eA eD) hun
  refine ⟨T, D', hDA.mono_right hD', hD'c, ?_, hDmap⟩
  change fanout (transitionParent ∅ ∅ D D' q eA eD) (mark A) = mark A
  funext i
  by_cases hi : i ∈ D \ D'
  · have hp : (eD ⟨i, hi⟩).1.val ∈ D := hD' (eD ⟨i, hi⟩).1.property
    have hpA : (eD ⟨i, hi⟩).1.val ∉ A :=
      fun h => Finset.disjoint_left.mp hDA h hp
    simp [fanout, transitionParent, hi, mark, hpA]
  · simp [fanout, transitionParent, hi]

/-- The final cell map completes A while preserving the surviving D singleton. -/
theorem exists_last_cell_step (q h : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h)
    (A : Finset (Cell q h)) (pivot : Cell q h)
    (hAD : Disjoint A ({pivot} : Finset (Cell q h))) (hAc : A.card = q ^ (h - 2)) :
    ∃ T : CellMap q h, T (mark A) = mark (Finset.univ.erase pivot) ∧
      T (mark {pivot}) = mark {pivot} := by
  classical
  let A' : Finset (Cell q h) := Finset.univ.erase pivot
  have hAA' : A ⊆ A' := by
    intro i hi
    have hne : i ≠ pivot := by
      intro he
      exact Finset.disjoint_left.mp hAD hi (by simp [he])
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hA'c : A'.card = A.card * q := by
    rw [hAc, ← first_compression_count q h hh]
    simp [A', Finset.card_erase_of_mem, cellSize]
  -- The surviving D site is idle within its cell in the last layer.
  obtain ⟨eA, eD, hun, hAmap, _⟩ :=
    exists_fanout_transition q (by omega) A A' ∅ ∅ hAA' (by simp) (by simp) hA'c (by simp)
  let T : CellMap q h := fanoutLinearEquiv (transitionParent A A' ∅ ∅ q eA eD) hun
  refine ⟨T, hAmap, ?_⟩
  change fanout (transitionParent A A' ∅ ∅ q eA eD)
    (mark ({pivot} : Finset (Cell q h))) = mark {pivot}
  funext i
  by_cases hi : i ∈ A' \ A
  · have hp : (eA ⟨i, hi⟩).1.val ∈ A := (eA ⟨i, hi⟩).1.property
    have hp' : (eA ⟨i, hi⟩).1.val ∉ ({pivot} : Finset (Cell q h)) :=
      Finset.disjoint_left.mp hAD hp
    simp [fanout, transitionParent, hi, mark, hp']
  · simp [fanout, transitionParent, hi]

/-- For h at least two the h within-cell linear maps carry the two input
parts to a complementary pair at output. -/
theorem exists_cell_schedule (q h : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h) (seed : Cell q h) :
    ∃ (steps : List (CellMap q h)) (pivot : Cell q h),
      steps.length = h ∧
      runCell steps (mark {seed}) = mark (Finset.univ.erase pivot) ∧
      runCell steps (mark (Finset.univ.erase seed)) = mark {pivot} := by
  obtain ⟨first, D₀, hdis, hc, hA₀, hD₀⟩ := exists_first_cell_step q h hq hh seed
  obtain ⟨middle, A₁, D₁, hmid, hdis₁, hAc, hDc, hA₁, hD₁⟩ :=
    exists_middle_cell_steps q h (h - 2) hq hh le_rfl {seed} D₀ hdis (by simp) hc
  have hDc' : D₁.card = 1 := by simpa using hDc
  obtain ⟨pivot, rfl⟩ := Finset.card_eq_one.mp hDc'
  obtain ⟨last, hAlast, hDlast⟩ := exists_last_cell_step q h hq hh A₁ pivot hdis₁ hAc
  refine ⟨first :: middle ++ [last], pivot, ?_, ?_, ?_⟩
  · simp [hmid]
    omega
  · rw [show first :: middle ++ [last] = (first :: middle) ++ [last] from rfl,
      runCell_append_step]
    change last (runCell middle (first (mark {seed}))) = _
    rw [hA₀, hA₁, hAlast]
  · rw [show first :: middle ++ [last] = (first :: middle) ++ [last] from rfl,
      runCell_append_step]
    change last (runCell middle (first (mark (Finset.univ.erase seed)))) = _
    rw [hD₀, hD₁, hDlast]

#print axioms exists_middle_cell_steps
#print axioms exists_first_cell_step
#print axioms exists_last_cell_step
#print axioms exists_cell_schedule

end CriticalDepth.FaultShorSaturation
