import ShorIndexedSchedule

/-!
# One cell schedule repeated on a physical register

An equivalence identifies every site with its block index and cell
coordinate. A lifted parent stays in the block of its target. Its
working support is an injective image of the local working support.
-/

namespace CriticalDepth.FaultShorSaturation

variable {n m q : ℕ} {β : Type*}

private def parentAcrossCells (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (i : Fin n) : Option (Fin n) :=
  (P.parent (e i).2).map (fun a => e.symm ((e i).1, a))

private theorem parentAcrossCells_some (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (i a : Fin n) :
    parentAcrossCells P e i = some a ↔ (e i).1 = (e a).1 ∧
      P.parent (e i).2 = some (e a).2 := by
  unfold parentAcrossCells
  cases h : P.parent (e i).2 with
  | none => simp
  | some b =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro he
        have hh : ((e i).1, b) = e a := (e.apply_symm_apply _).symm.trans (congrArg e he)
        have hf : (((e i).1, b) : β × Fin m).1 = (e a).1 := congrArg Prod.fst hh
        have hs : (((e i).1, b) : β × Fin m).2 = (e a).2 := congrArg Prod.snd hh
        exact ⟨hf, hs⟩
      · intro he
        have hh : ((e i).1, b) = e a := Prod.ext he.1 he.2
        rw [hh, Equiv.symm_apply_apply]

private theorem parentAcrossCells_none (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (i : Fin n) :
    parentAcrossCells P e i = none ↔ P.parent (e i).2 = none := by
  unfold parentAcrossCells
  cases P.parent (e i).2 <;> simp

private def cellEmbedding (e : Fin n ≃ β × Fin m) (b : β) : Fin m ↪ Fin n where
  toFun i := e.symm (b, i)
  inj' := fun _ _ h => congrArg Prod.snd (e.symm.injective h)

private theorem parentAcrossCells_sites (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (a : Fin n) :
    parentSites (parentAcrossCells P e) a =
      (parentSites P.parent (e a).2).map (cellEmbedding e (e a).1) := by
  classical
  ext i
  rw [parentSites_mem]
  constructor
  · rintro (h | hi)
    · subst i
      refine Finset.mem_map.mpr ⟨(e a).2, (parentSites_mem _ _ _).mpr (.inl rfl), ?_⟩
      exact e.symm_apply_apply a
    · obtain ⟨hi₁, hi₂⟩ := (parentAcrossCells_some P e i a).mp hi
      refine Finset.mem_map.mpr ⟨(e i).2, (parentSites_mem _ _ _).mpr (.inr hi₂), ?_⟩
      change e.symm ((e a).1, (e i).2) = i
      rw [← hi₁]
      exact e.symm_apply_apply i
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
    change e.symm ((e a).1, j) = i at he
    have hpair : ((e a).1, j) = e i := (e.apply_symm_apply _).symm.trans (congrArg e he)
    have hf : (e i).1 = (e a).1 := (congrArg Prod.fst hpair).symm
    have hs : j = (e i).2 := congrArg Prod.snd hpair
    rcases (parentSites_mem _ _ _).mp hj with h | h
    · exact .inl (e.injective (Prod.ext hf (hs.symm.trans h)))
    · exact .inr ((parentAcrossCells_some P e i a).mpr ⟨hf, hs ▸ h⟩)

/-- Lift one bounded cell step to every block of a finite physical register. -/
def CellParent.liftCells (P : CellParent m q) (e : Fin n ≃ β × Fin m) :
    CellParent n q where
  parent := parentAcrossCells P e
  untouched i a hi :=
    (parentAcrossCells_none P e a).mpr
      (P.untouched _ _ ((parentAcrossCells_some P e i a).mp hi).2)
  arity a := by
    rw [parentAcrossCells_sites, Finset.card_map]
    exact P.arity _

theorem CellParent.liftCells_parent_some (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (i a : Fin n) :
    (P.liftCells e).parent i = some a ↔ (e i).1 = (e a).1 ∧
      P.parent (e i).2 = some (e a).2 :=
  parentAcrossCells_some P e i a

theorem CellParent.liftCells_idle (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (i : Fin n) (hi : P.Idle (e i).2) : (P.liftCells e).Idle i := by
  refine ⟨(parentAcrossCells_none P e i).mpr hi.1, ?_⟩
  intro j hj
  exact hi.2 (e j).2 ((parentAcrossCells_some P e j i).mp hj).2

theorem CellParent.liftCells_run (P : CellParent m q) (e : Fin n ≃ β × Fin m)
    (v : Fin n → Bit) (b : β) (i : Fin m) :
    (P.liftCells e).run v (e.symm (b, i)) =
      P.run (fun j => v (e.symm (b, j))) i := by
  have hs : e (e.symm (b, i)) = (b, i) := e.apply_symm_apply _
  rw [CellParent.run_apply, CellParent.run_apply]
  have hp : (P.liftCells e).parent (e.symm (b, i)) =
      (P.parent i).map (fun a => e.symm (b, a)) := by
    change (P.parent (e (e.symm (b, i))).2).map
      (fun a => e.symm ((e (e.symm (b, i))).1, a)) = _
    rw [hs]
  cases h : P.parent i <;> simp [fanout, hp, h]

/-- Run a shared schedule in each physical cell simultaneously. -/
theorem runParents_liftCells (steps : List (CellParent m q)) (e : Fin n ≃ β × Fin m)
    (v : Fin n → Bit) (b : β) (i : Fin m) :
    runParents (steps.map fun P => P.liftCells e) v (e.symm (b, i)) =
      runParents steps (fun j => v (e.symm (b, j))) i := by
  induction steps generalizing v with
  | nil => rfl
  | cons P steps ih =>
      change runParents (steps.map fun S => S.liftCells e) ((P.liftCells e).run v)
        (e.symm (b, i)) = runParents steps (P.run (fun j => v (e.symm (b, j)))) i
      rw [ih]
      have hs : (fun j => (P.liftCells e).run v (e.symm (b, j))) =
          P.run (fun j => v (e.symm (b, j))) := funext (P.liftCells_run e v b)
      rw [hs]

#print axioms CellParent.liftCells
#print axioms CellParent.liftCells_idle
#print axioms runParents_liftCells

end CriticalDepth.FaultShorSaturation
