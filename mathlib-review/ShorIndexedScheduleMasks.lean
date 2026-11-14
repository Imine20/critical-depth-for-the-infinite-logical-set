import ShorIndexedScheduleLift

/-!
# Mask action of the repeated rectangular Shor cell schedule

The two uniform cell masks are repeated on every selected block. The
terminal words partition the register. Repeating the chosen schedule
therefore preserves the all-ones word.
-/

namespace CriticalDepth.FaultShorSaturation

variable {n m q : ℕ} {β : Type*}

/-- A bit word with the same local pattern on every cell. -/
def repeatCellWord (e : Fin n ≃ β × Fin m) (v : Fin m → Bit) : Fin n → Bit :=
  fun i => v (e i).2

theorem repeatCellWord_apply_symm (e : Fin n ≃ β × Fin m) (v : Fin m → Bit)
    (b : β) (i : Fin m) : repeatCellWord e v (e.symm (b, i)) = v i := by
  unfold repeatCellWord
  rw [e.apply_symm_apply]

theorem CellParent.liftCells_run_repeat (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (v : Fin m → Bit) :
    (P.liftCells e).run (repeatCellWord e v) = repeatCellWord e (P.run v) := by
  funext i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.symm.surjective i
  rw [P.liftCells_run, repeatCellWord_apply_symm]
  have hw : (fun k => repeatCellWord e v (e.symm (b, k))) = v :=
    funext (repeatCellWord_apply_symm e v b)
  rw [hw]

theorem runParents_liftCells_repeat (steps : List (CellParent m q)) (e : Fin n ≃ β × Fin m)
    (v : Fin m → Bit) :
    runParents (steps.map fun P => P.liftCells e) (repeatCellWord e v) =
      repeatCellWord e (runParents steps v) := by
  funext i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.symm.surjective i
  rw [runParents_liftCells, repeatCellWord_apply_symm]
  have hw : (fun k => repeatCellWord e v (e.symm (b, k))) = v :=
    funext (repeatCellWord_apply_symm e v b)
  rw [hw]

theorem runParents_add (steps : List (CellParent m q)) (u v : Fin m → Bit) :
    runParents steps (u + v) = runParents steps u + runParents steps v := by
  induction steps generalizing u v with
  | nil => rfl
  | cons P steps ih =>
      change runParents steps (P.run (u + v)) =
        runParents steps (P.run u) + runParents steps (P.run v)
      rw [map_add, ih]

private theorem mark_singleton_add_erase (i : Fin m) :
    mark ({i} : Finset (Fin m)) + mark (Finset.univ.erase i) = (1 : Fin m → Bit) := by
  funext j
  by_cases hij : j = i
  · subst j
    simp [mark, Pi.add_apply]
  · simp [mark, Pi.add_apply, hij]

theorem IndexedCellSchedule.runParents_ones {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) :
    runParents S.steps 1 = 1 := by
  calc
    runParents S.steps 1 =
        runParents S.steps (mark {seed} + mark (Finset.univ.erase seed)) :=
      congrArg (runParents S.steps) (mark_singleton_add_erase seed).symm
    _ = mark (Finset.univ.erase S.pivot) + mark {S.pivot} := by
      rw [runParents_add, S.a_out, S.d_out]
    _ = 1 := by
      rw [add_comm]
      exact mark_singleton_add_erase S.pivot

theorem IndexedCellSchedule.lifted_ones {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (e : Fin n ≃ β × Cell q h) :
    runParents (S.steps.map fun P => P.liftCells e) 1 = 1 := by
  change runParents (S.steps.map fun P => P.liftCells e) (repeatCellWord e 1) =
    repeatCellWord e 1
  rw [runParents_liftCells_repeat, S.runParents_ones]

theorem IndexedCellSchedule.lifted_a_out {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (e : Fin n ≃ β × Cell q h) :
    runParents (S.steps.map fun P => P.liftCells e) (repeatCellWord e (mark {seed})) =
      repeatCellWord e (mark (Finset.univ.erase S.pivot)) := by
  rw [runParents_liftCells_repeat, S.a_out]

theorem IndexedCellSchedule.lifted_d_out {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (e : Fin n ≃ β × Cell q h) :
    runParents (S.steps.map fun P => P.liftCells e)
        (repeatCellWord e (mark (Finset.univ.erase seed))) =
      repeatCellWord e (mark {S.pivot}) := by
  rw [runParents_liftCells_repeat, S.d_out]

#print axioms IndexedCellSchedule.lifted_ones
#print axioms IndexedCellSchedule.lifted_a_out
#print axioms IndexedCellSchedule.lifted_d_out


/-- Repeat a local bit word exactly in the chosen cells. -/
def liftCellWord (e : Fin n ≃ β × Fin m) (choose : β → Bool)
    (v : Fin m → Bit) : Fin n → Bit :=
  fun i => if choose (e i).1 then v (e i).2 else 0

theorem liftCellWord_apply_symm (e : Fin n ≃ β × Fin m) (choose : β → Bool)
    (v : Fin m → Bit) (b : β) (i : Fin m) :
    liftCellWord e choose v (e.symm (b, i)) = if choose b then v i else 0 := by
  unfold liftCellWord
  rw [e.apply_symm_apply]

theorem liftCellWord_all (e : Fin n ≃ β × Fin m) (v : Fin m → Bit) :
    liftCellWord e (fun _ => true) v = repeatCellWord e v := by
  funext i
  simp [liftCellWord, repeatCellWord]

theorem runParents_zero (steps : List (CellParent m q)) :
    runParents steps 0 = 0 := by
  induction steps with
  | nil => rfl
  | cons P steps ih =>
      change runParents steps (P.run 0) = 0
      rw [map_zero, ih]

theorem runParents_liftCellWord (steps : List (CellParent m q))
    (e : Fin n ≃ β × Fin m) (choose : β → Bool) (v : Fin m → Bit) :
    runParents (steps.map fun P => P.liftCells e) (liftCellWord e choose v) =
      liftCellWord e choose (runParents steps v) := by
  funext i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.symm.surjective i
  rw [runParents_liftCells, liftCellWord_apply_symm]
  cases h : choose b with
  | false =>
      have hw : (fun k => liftCellWord e choose v (e.symm (b, k))) = 0 := by
        funext k
        simp [liftCellWord_apply_symm, h]
      rw [hw, runParents_zero]
      simp [h]
  | true =>
      have hw : (fun k => liftCellWord e choose v (e.symm (b, k))) = v := by
        funext k
        simp [liftCellWord_apply_symm, h]
      rw [hw]
      simp [h]

theorem liftCellWord_add (e : Fin n ≃ β × Fin m) (choose : β → Bool)
    (u v : Fin m → Bit) :
    liftCellWord e choose (u + v) = liftCellWord e choose u + liftCellWord e choose v := by
  funext i
  cases h : choose (e i).1 <;> simp [liftCellWord, Pi.add_apply, h]

/-- The first layer preserves the seed mask in all selected cells. -/
theorem IndexedCellSchedule.lifted_seed_after_first {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (e : Fin n ≃ β × Cell q h) (choose : β → Bool) :
    (S.first.liftCells e).run (liftCellWord e choose (mark {seed})) =
      liftCellWord e choose (mark {seed}) := by
  have ht := runParents_liftCellWord [S.first] e choose (mark {seed})
  change (S.first.liftCells e).run (liftCellWord e choose (mark {seed})) =
    liftCellWord e choose (S.first.run (mark {seed})) at ht
  rw [S.seed_after_first] at ht
  exact ht

/-- The fault inserted at the seed after layer one propagates through the tail. -/
theorem IndexedCellSchedule.lifted_seed_through_tail {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (e : Fin n ≃ β × Cell q h) (choose : β → Bool) :
    runParents ((S.middle ++ [S.last]).map fun P => P.liftCells e)
        (liftCellWord e choose (mark {seed})) =
      liftCellWord e choose (mark (Finset.univ.erase S.pivot)) := by
  have ha := S.a_out
  rw [show S.steps = S.first :: (S.middle ++ [S.last]) from rfl] at ha
  change runParents (S.middle ++ [S.last]) (S.first.run (mark {seed})) =
    mark (Finset.univ.erase S.pivot) at ha
  rw [S.seed_after_first] at ha
  rw [runParents_liftCellWord, ha]

theorem IndexedCellSchedule.lifted_d_before_last {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (e : Fin n ≃ β × Cell q h) (choose : β → Bool) :
    runParents ((S.first :: S.middle).map fun P => P.liftCells e)
        (liftCellWord e choose (mark (Finset.univ.erase seed))) =
      liftCellWord e choose (mark {S.pivot}) := by
  rw [runParents_liftCellWord, S.d_before_last]

theorem IndexedCellSchedule.lifted_selected_partition {h : ℕ} {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (e : Fin n ≃ β × Cell q h) (choose : β → Bool) :
    liftCellWord e choose (mark (Finset.univ.erase S.pivot)) +
        liftCellWord e choose (mark {S.pivot}) = liftCellWord e choose 1 := by
  rw [← liftCellWord_add, add_comm]
  rw [mark_singleton_add_erase]

#print axioms runParents_liftCellWord
#print axioms IndexedCellSchedule.lifted_seed_through_tail
#print axioms IndexedCellSchedule.lifted_d_before_last
#print axioms IndexedCellSchedule.lifted_selected_partition

end CriticalDepth.FaultShorSaturation
