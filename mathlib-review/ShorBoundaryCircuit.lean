import ShorGroupLayout
import ShorCycleAction
import ShorIndexedScheduleMasks

/-!
# The grouped binary circuit

A boundary layer acts by the marked-site cycles followed by the
within-cell fanout. Intermediate layers contain only the fanout.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript

variable {g q h c : ℕ}

abbrev GroupCellIndex (g q c : ℕ) := (Fin g × Fin q) × Fin c

noncomputable def shorBoundaryLayer (P : CellParent (cellSize q h) q)
    (p : Cell q h) (hidle : P.Idle p) :
    ArbitraryLayer (ShorSites g q h c) (fun _ => 2) q :=
  let e := shorCellLayout g q h c
  let Q := P.liftCells e
  cycleAndParentLayer (shorCycleBlocks g q h c p) (shorCycleBlocks_pairwise p)
    Q.parent Q.untouched Q.arity (by
      intro B hB i hi
      unfold shorCycleBlocks at hB
      obtain ⟨ij, _, hB⟩ := List.mem_map.mp hB
      subst B
      have hp := ((mem_shorCycle_sites ij.1 ij.2 p i).mp hi).2.2
      exact P.liftCells_idle e i (hp.symm ▸ hidle))

noncomputable def shorBoundaryRun (P : CellParent (cellSize q h) q) (p : Cell q h) :
    (Fin (ShorSites g q h c) → Bit) ≃ₗ[Bit] (Fin (ShorSites g q h c) → Bit) :=
  (siteCyclesLinearEquiv (shorCycleBlocks g q h c p)).trans
    ((P.liftCells (shorCellLayout g q h c)).run)

theorem shorBoundaryLayer_has_cycle_slot (P : CellParent (cellSize q h) q)
    (p : Cell q h) (hidle : P.Idle p) (i : Fin g) (j : Fin c) (hq : 0 < q) :
    ∃ a : Fin (ShorSites g q h c),
      (shorBoundaryLayer P p hidle).normalized.support a = (shorCycle i j p).sites := by
  apply ArbitraryLayer.exists_normalized_support _ (shorCycle i j p).gate
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨_, shorCycle_mem_blocks i j p, rfl⟩
  · exact shorCycle_nonempty i j p hq

theorem siteCyclesLinearEquiv_shor_liftCellWord (p : Cell q h)
    (v : Cell q h → Bit) (choice : Fin c → Bool) :
    siteCyclesLinearEquiv (shorCycleBlocks g q h c p)
        (liftCellWord (shorCellLayout g q h c) (fun b => choice b.2) v) =
      liftCellWord (shorCellLayout g q h c) (fun b => choice b.2) v := by
  change siteCyclesWordEquiv _ _ = _
  rw [siteCyclesWordEquiv_apply]
  apply runSiteCycles_fixes
  intro B hB i hi k hk
  unfold shorCycleBlocks at hB
  obtain ⟨ij, _, hB⟩ := List.mem_map.mp hB
  subst B
  obtain ⟨_, hic, hip⟩ := (mem_shorCycle_sites ij.1 ij.2 p i).mp hi
  obtain ⟨_, hkc, hkp⟩ := (mem_shorCycle_sites ij.1 ij.2 p k).mp hk
  simp [liftCellWord, hic, hip, hkc, hkp]

theorem shorBoundaryRun_liftCellWord (P : CellParent (cellSize q h) q) (p : Cell q h)
    (v : Cell q h → Bit) (choice : Fin c → Bool) :
    shorBoundaryRun (g := g) P p
        (liftCellWord (shorCellLayout g q h c) (fun b => choice b.2) v) =
      (P.liftCells (shorCellLayout g q h c)).run
        (liftCellWord (shorCellLayout g q h c) (fun b => choice b.2) v) := by
  change (P.liftCells (shorCellLayout g q h c)).run
    (siteCyclesLinearEquiv (shorCycleBlocks g q h c p)
      (liftCellWord (shorCellLayout g q h c) (fun b => choice b.2) v)) = _
  rw [siteCyclesLinearEquiv_shor_liftCellWord]

#print axioms shorBoundaryLayer_has_cycle_slot
#print axioms shorBoundaryRun_liftCellWord

end CriticalDepth.FaultShorSaturation