import ShorGroupedCircuit

/-!
# The Shor circuit fixes the encoding and propagates the seed fault

The only extra maps in the first and last layers are uniform on the
repeated masks being tracked. This makes the binary endpoint equations
for the cell schedule apply verbatim on the full physical register.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

variable {g q h c : ℕ} {seed : Cell q h}

theorem shorTailRun_liftCellWord (S : IndexedCellSchedule q h seed)
    (v : Cell q h → Bit) (choose : Fin c → Bool) :
    shorTailRun S (liftCellWord (shorCellLayout g q h c) (fun b => choose b.2) v) =
      runParents ((S.middle ++ [S.last]).map fun P => P.liftCells (shorCellLayout g q h c))
        (liftCellWord (shorCellLayout g q h c) (fun b => choose b.2) v) := by
  let E := shorCellLayout g q h c
  let selection : GroupCellIndex g q c → Bool := fun b => choose b.2
  let middle := S.middle.map fun P => P.liftCells E
  change shorBoundaryRun S.last S.pivot (parentSequenceRun middle (liftCellWord E selection v)) = _
  rw [parentSequenceRun_apply, runParents_liftCellWord, shorBoundaryRun_liftCellWord]
  rw [List.map_append, List.map_cons, List.map_nil, runParents_append_step, runParents_liftCellWord]

theorem shorGroupedRun_liftCellWord (S : IndexedCellSchedule q h seed)
    (v : Cell q h → Bit) (choose : Fin c → Bool) :
    shorGroupedRun S (liftCellWord (shorCellLayout g q h c) (fun b => choose b.2) v) =
      runParents (S.steps.map fun P => P.liftCells (shorCellLayout g q h c))
        (liftCellWord (shorCellLayout g q h c) (fun b => choose b.2) v) := by
  let E := shorCellLayout g q h c
  let selection : GroupCellIndex g q c → Bool := fun b => choose b.2
  change shorTailRun S (shorBoundaryRun S.first seed (liftCellWord E selection v)) = _
  rw [shorBoundaryRun_liftCellWord]
  have hfirst := runParents_liftCellWord [S.first] E selection v
  change (S.first.liftCells E).run (liftCellWord E selection v) =
    liftCellWord E selection (S.first.run v) at hfirst
  rw [hfirst, shorTailRun_liftCellWord]
  rw [show S.steps = S.first :: (S.middle ++ [S.last]) from rfl, List.map_cons]
  change _ = runParents _ ((S.first.liftCells E).run (liftCellWord E selection v))
  rw [hfirst]

theorem shorTailRun_seed (S : IndexedCellSchedule q h seed) (j : Fin c) :
    shorTailRun S (liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) (mark {seed})) =
      liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) (mark (Finset.univ.erase S.pivot)) := by
  unfold chooseShorColumn
  rw [shorTailRun_liftCellWord (g := g) S (mark {seed}) (fun k => decide (k = j))]
  exact S.lifted_seed_through_tail (shorCellLayout g q h c) (chooseShorColumn j)

theorem shorGroupedRun_ones (S : IndexedCellSchedule q h seed) :
    shorGroupedRun (g := g) (c := c) S 1 = 1 := by
  let E := shorCellLayout g q h c
  have hone : liftCellWord E (fun _ => true) 1 = 1 := by
    funext i
    rfl
  calc
    shorGroupedRun (g := g) (c := c) S 1 = shorGroupedRun S (liftCellWord E (fun _ => true) 1) :=
      congrArg (shorGroupedRun S) hone.symm
    _ = _ := by
      calc
        _ = runParents (S.steps.map fun P => P.liftCells E) (liftCellWord E (fun _ => true) 1) :=
          shorGroupedRun_liftCellWord (g := g) S 1 (fun _ : Fin c => true)
        _ = 1 := by rw [hone]; exact S.lifted_ones E

theorem parentSequenceRun_acrossColumns
    (ps : List (CellParent (cellSize q h) q)) :
    parentSequenceRun (ps.map fun P => P.liftCells (shorCellLayout g q h c)) =
      acrossColumnsPhysicalLinearEquiv (columns := c)
        (parentSequenceRun (ps.map fun P => P.liftCells (groupedRowCellLayout g q h))) := by
  induction ps with
  | nil =>
    apply eq_acrossColumnsPhysicalLinearEquiv
    intro x i j
    rfl
  | cons P ps ih =>
    simp only [List.map_cons, parentSequenceRun, CellParent.liftCells_shorColumn, ih,
      acrossColumnsPhysical_trans]

theorem exists_shorGroupedRun_row (S : IndexedCellSchedule q h seed) (j₀ : Fin c) :
    ∃ T : (Fin (ShorRows g q h) → Bit) ≃ₗ[Bit] (Fin (ShorRows g q h) → Bit),
      T 1 = 1 ∧ shorGroupedRun (g := g) (c := c) S =
        acrossColumnsPhysicalLinearEquiv (columns := c) T := by
  obtain ⟨T, hT⟩ := exists_shorBoundaryRun_row (g := g) S.first seed j₀
  obtain ⟨U, hU⟩ := exists_shorBoundaryRun_row (g := g) S.last S.pivot j₀
  let M := parentSequenceRun (S.middle.map fun P => P.liftCells (groupedRowCellLayout g q h))
  have he : shorGroupedRun (g := g) (c := c) S =
      acrossColumnsPhysicalLinearEquiv (columns := c) (T.trans (M.trans U)) := by
    unfold shorGroupedRun shorTailRun
    rw [hT, hU, parentSequenceRun_acrossColumns, acrossColumnsPhysical_trans, acrossColumnsPhysical_trans]
  refine ⟨_, (acrossColumnsPhysicalLinearEquiv_fixes_one_iff _ j₀).mp ?_, he⟩
  rw [← he]
  exact shorGroupedRun_ones S

theorem shorGroupedCircuit_implements_one (S : IndexedCellSchedule q h seed)
    (r : Fin (ShorRows g q h)) (j₀ : Fin (c + 1)) (hq : 0 < q) :
    Implements (physicalShorCode (columns := c) r)
      (layerSequenceEval (shorGroupedCircuit (g := g) (c := c + 1) S)) 1 := by
  obtain ⟨T, hT, he⟩ := exists_shorGroupedRun_row (g := g) S j₀
  apply physicalShorCode_implements_one_of_acrossColumns r T hT
  rw [shorGroupedCircuit_eval _ hq, he]

#print axioms shorTailRun_seed
#print axioms shorGroupedCircuit_implements_one

end CriticalDepth.FaultShorSaturation