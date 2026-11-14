import FaultShorScheduleIteration
import ShorNativeTransitionArity

/-!
# A bounded fanout cell schedule with idle boundary sites

Each step retains its parent assignments and the arity of every resulting
gate. The first seed and the last surviving representative are idle in
their respective fanout layers, so either layer can also contain gates
on those sites.
-/

namespace CriticalDepth.FaultShorSaturation

/-- Parent assignments of one simultaneous fanout on a finite site type. -/
structure CellParent (n q : ℕ) where
  parent : Fin n → Option (Fin n)
  untouched : ∀ i a, parent i = some a → parent a = none
  arity : ∀ a, (parentSites parent a).card ≤ q

def CellParent.Idle {n q : ℕ} (P : CellParent n q) (i : Fin n) : Prop :=
  P.parent i = none ∧ ∀ j, P.parent j ≠ some i

def CellParent.run {n q : ℕ} (P : CellParent n q) : (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit) :=
  fanoutLinearEquiv P.parent P.untouched

theorem CellParent.run_apply {n q : ℕ} (P : CellParent n q) (v : Fin n → Bit) :
    P.run v = fanout P.parent v := rfl

theorem CellParent.idle_mark {n q : ℕ} (P : CellParent n q) (i : Fin n)
    (hi : P.Idle i) : P.run (mark {i}) = mark {i} := by
  rw [P.run_apply]
  funext j
  cases hj : P.parent j with
  | none => simp [fanout, hj]
  | some a =>
      have ha : a ≠ i := fun h => hi.2 j (h ▸ hj)
      simp [fanout, hj, mark, ha]

def runParents {n q : ℕ} (steps : List (CellParent n q))
    (v : Fin n → Bit) : Fin n → Bit :=
  steps.foldl (fun x P => P.run x) v

theorem runParents_append {n q : ℕ} (a b : List (CellParent n q))
    (v : Fin n → Bit) : runParents (a ++ b) v = runParents b (runParents a v) := by
  simp [runParents, List.foldl_append]

theorem runParents_append_step {n q : ℕ} (steps : List (CellParent n q))
    (P : CellParent n q) (v : Fin n → Bit) :
    runParents (steps ++ [P]) v = P.run (runParents steps v) := by
  rw [runParents_append]
  rfl

private theorem transition_idle {n q : ℕ} (A A' D D' : Finset (Fin n))
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (eA : (A' \ A : Finset (Fin n)) ≃ A × Fin (q - 1))
    (eD : (D \ D' : Finset (Fin n)) ≃ D' × Fin (q - 1))
    (hun : ∀ i a, transitionParent A A' D D' q eA eD i = some a →
      transitionParent A A' D D' q eA eD a = none)
    (hq : 1 ≤ q) (i : Fin n) (hiA : i ∉ A') (hiD : i ∉ D) :
    (⟨transitionParent A A' D D' q eA eD, hun,
      transitionParent_arity q hq A A' D D' hAA' hD'D hA'D eA eD⟩ : CellParent n q).Idle i := by
  classical
  change transitionParent A A' D D' q eA eD i = none ∧
    ∀ j, transitionParent A A' D D' q eA eD j ≠ some i
  refine ⟨by simp [transitionParent, hiA, hiD], ?_⟩
  intro j hj
  by_cases hA : j ∈ A' \ A
  · have he : (eA ⟨j, hA⟩).1.val = i := by simpa [transitionParent, hA] using hj
    exact hiA (he ▸ hAA' (eA ⟨j, hA⟩).1.property)
  · by_cases hD : j ∈ D \ D'
    · have he : (eD ⟨j, hD⟩).1.val = i := by simpa [transitionParent, hA, hD] using hj
      exact hiD (he ▸ hD'D (eD ⟨j, hD⟩).1.property)
    · simp [transitionParent, hA, hD] at hj

/-- The first cell layer compresses the complement of the seed. -/
theorem exists_first_parent_step (q h : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h)
    (seed : Cell q h) :
    ∃ (P : CellParent (cellSize q h) q) (D : Finset (Cell q h)),
      P.Idle seed ∧ Disjoint ({seed} : Finset (Cell q h)) D ∧ D.card = q ^ (h - 2) ∧
      P.run (mark (Finset.univ.erase seed)) = mark D := by
  classical
  let D₀ : Finset (Cell q h) := Finset.univ.erase seed
  have hDc : D₀.card = q ^ (h - 1) := by
    simp [D₀, Finset.card_erase_of_mem, cellSize]
  have hbound : q ^ (h - 2) ≤ D₀.card := by
    rw [hDc]
    exact pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
  obtain ⟨D, hD, hDc'⟩ := Finset.exists_subset_card_eq hbound
  have h₁ : 1 ≤ q := by omega
  have hcard : D₀.card = D.card * q := by
    rw [hDc, hDc', first_compression_count q h hh]
  obtain ⟨eA, eD, hun, _, hmap⟩ :=
    exists_fanout_transition q h₁ (∅ : Finset (Cell q h)) ∅ D₀ D
      (by simp) hD (by simp) (by simp) hcard
  let P : CellParent (cellSize q h) q :=
    ⟨transitionParent ∅ ∅ D₀ D q eA eD, hun,
      transitionParent_arity q h₁ ∅ ∅ D₀ D (by simp) hD (by simp) eA eD⟩
  refine ⟨P, D, ?_, ?_, hDc', hmap⟩
  · exact transition_idle ∅ ∅ D₀ D (by simp) hD (by simp) eA eD hun h₁ seed
      (by simp) (by simp [D₀])
  · apply Finset.disjoint_left.mpr
    intro i hi hiD
    have he : i = seed := Finset.mem_singleton.mp hi
    exact (Finset.mem_erase.mp (hD hiD)).1 he

/-- A simultaneous middle layer expands A and compresses D with certified arity. -/
theorem exists_middle_parent_step (q h j : ℕ)
    (hq : 2 ≤ q) (hj : 2 ≤ j) (hjh : j < h)
    (A D : Finset (Cell q h)) (hAD : Disjoint A D)
    (hA : A.card = q ^ (j - 2)) (hD : D.card = q ^ (h - j)) :
    ∃ (P : CellParent (cellSize q h) q) (A' D' : Finset (Cell q h)),
      A'.card = q ^ (j - 1) ∧ D'.card = q ^ (h - j - 1) ∧ Disjoint A' D' ∧
      P.run (mark A) = mark A' ∧ P.run (mark D) = mark D' := by
  obtain ⟨A', D', hAA', hD'D, hA'D, hAc, hDc⟩ :=
    exists_intermediate_support_step q h j hq hj hjh A D hAD hA hD
  have h₁ : 1 ≤ q := by omega
  have hAcard : A'.card = A.card * q := by
    rw [hAc, hA, intermediate_expansion_count q j hj]
  have hDcard : D.card = D'.card * q := by
    rw [hD, hDc, intermediate_compression_count q h j hjh]
  obtain ⟨eA, eD, hun, hmapA, hmapD⟩ :=
    exists_fanout_transition q h₁ A A' D D' hAA' hD'D hA'D hAcard hDcard
  exact ⟨⟨transitionParent A A' D D' q eA eD, hun,
    transitionParent_arity q h₁ A A' D D' hAA' hD'D hA'D eA eD⟩,
    A', D', hAc, hDc, hA'D.mono_right hD'D, hmapA, hmapD⟩

/-- The last cell layer expands A while its remaining D site is idle. -/
theorem exists_last_parent_step (q h : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h)
    (A : Finset (Cell q h)) (pivot : Cell q h)
    (hAD : Disjoint A ({pivot} : Finset (Cell q h))) (hAc : A.card = q ^ (h - 2)) :
    ∃ (P : CellParent (cellSize q h) q),
      P.Idle pivot ∧ P.run (mark A) = mark (Finset.univ.erase pivot) := by
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
  have h₁ : 1 ≤ q := by omega
  obtain ⟨eA, eD, hun, hmap, _⟩ :=
    exists_fanout_transition q h₁ A A' ∅ ∅ hAA' (by simp) (by simp) hA'c (by simp)
  let P : CellParent (cellSize q h) q :=
    ⟨transitionParent A A' ∅ ∅ q eA eD, hun,
      transitionParent_arity q h₁ A A' ∅ ∅ hAA' (by simp) (by simp) eA eD⟩
  exact ⟨P, transition_idle A A' ∅ ∅ hAA' (by simp) (by simp) eA eD hun h₁ pivot
    (by simp [A']) (by simp), hmap⟩

theorem exists_middle_parent_steps (q h j : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h)
    (hj : j ≤ h - 2) (A D : Finset (Cell q h)) (hAD : Disjoint A D)
    (hA : A.card = 1) (hD : D.card = q ^ (h - 2)) :
    ∃ (steps : List (CellParent (cellSize q h) q)) (A' D' : Finset (Cell q h)),
      steps.length = j ∧ Disjoint A' D' ∧ A'.card = q ^ j ∧
      D'.card = q ^ (h - 2 - j) ∧
      runParents steps (mark A) = mark A' ∧ runParents steps (mark D) = mark D' := by
  induction j with
  | zero =>
      exact ⟨[], A, D, rfl, hAD, by simpa using hA, by simpa using hD, rfl, rfl⟩
  | succ j ih =>
      obtain ⟨steps, A', D', hlen, hdis, hAc, hDc, hAV, hDV⟩ := ih (by omega)
      have hD' : D'.card = q ^ (h - (j + 2)) := by
        rw [hDc, show h - 2 - j = h - (j + 2) by omega]
      obtain ⟨P, A'', D'', hA'', hD'', hdis', hX, hZ⟩ :=
        exists_middle_parent_step q h (j + 2) hq (by omega) (by omega)
          A' D' hdis (by simpa using hAc) hD'
      refine ⟨steps ++ [P], A'', D'', by simp [hlen], hdis',
        by simpa [show j + 2 - 1 = j + 1 by omega] using hA'',
        by simpa [show h - (j + 2) - 1 = h - 2 - (j + 1) by omega] using hD'', ?_, ?_⟩
      · rw [runParents_append_step, hAV, hX]
      · rw [runParents_append_step, hDV, hZ]

/-- A single set of cell choices is reused throughout the rectangle. -/
structure IndexedCellSchedule (q h : ℕ) (seed : Cell q h) where
  first : CellParent (cellSize q h) q
  middle : List (CellParent (cellSize q h) q)
  last : CellParent (cellSize q h) q
  pivot : Cell q h
  A : Finset (Cell q h)
  middle_length : middle.length = h - 2
  first_idle : first.Idle seed
  last_idle : last.Idle pivot
  a_before_last : runParents (first :: middle) (mark {seed}) = mark A
  d_before_last : runParents (first :: middle) (mark (Finset.univ.erase seed)) = mark {pivot}
  a_last : last.run (mark A) = mark (Finset.univ.erase pivot)

def IndexedCellSchedule.steps {q h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) : List (CellParent (cellSize q h) q) :=
  (S.first :: S.middle) ++ [S.last]

theorem IndexedCellSchedule.steps_length {q h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (hh : 2 ≤ h) : S.steps.length = h := by
  simp [IndexedCellSchedule.steps, S.middle_length]
  omega

theorem IndexedCellSchedule.seed_after_first {q h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) : S.first.run (mark {seed}) = mark {seed} :=
  S.first.idle_mark seed S.first_idle

theorem IndexedCellSchedule.a_out {q h : ℕ} {seed : Cell q h} (S : IndexedCellSchedule q h seed) :
    runParents S.steps (mark {seed}) = mark (Finset.univ.erase S.pivot) := by
  rw [IndexedCellSchedule.steps, runParents_append_step, S.a_before_last, S.a_last]

theorem IndexedCellSchedule.d_out {q h : ℕ} {seed : Cell q h} (S : IndexedCellSchedule q h seed) :
    runParents S.steps (mark (Finset.univ.erase seed)) = mark {S.pivot} := by
  rw [IndexedCellSchedule.steps, runParents_append_step, S.d_before_last]
  exact S.last.idle_mark S.pivot S.last_idle

theorem exists_indexedCellSchedule (q h : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h) (seed : Cell q h) :
    Nonempty (IndexedCellSchedule q h seed) := by
  obtain ⟨first, D₀, idleA, hdis, hDc, hDmap⟩ := exists_first_parent_step q h hq hh seed
  obtain ⟨middle, A, D, hmid, hdis', hAc, hDc', hAmap, hDmap'⟩ :=
    exists_middle_parent_steps q h (h - 2) hq hh le_rfl {seed} D₀ hdis (by simp) hDc
  have hDcard : D.card = 1 := by simpa using hDc'
  obtain ⟨pivot, rfl⟩ := Finset.card_eq_one.mp hDcard
  obtain ⟨last, idleD, hAout⟩ := exists_last_parent_step q h hq hh A pivot hdis' hAc
  refine ⟨⟨first, middle, last, pivot, A, hmid, idleA, idleD, ?_, ?_, hAout⟩⟩
  · change runParents middle (first.run (mark {seed})) = mark A
    rw [first.idle_mark seed idleA, hAmap]
  · change runParents middle (first.run (mark (Finset.univ.erase seed))) = mark {pivot}
    rw [hDmap, hDmap']

#print axioms exists_indexedCellSchedule
#print axioms IndexedCellSchedule.a_out
#print axioms IndexedCellSchedule.d_out

end CriticalDepth.FaultShorSaturation
