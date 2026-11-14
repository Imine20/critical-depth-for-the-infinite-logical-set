import ShorIndexedScheduleMasks
import ShorGroupLayout
import ShorRowActionColumns

/-!
# First-column masks in the grouped rectangular layout
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript

variable {g q h c : ℕ}

/-- The mask used for faults in exactly one selected column. -/
def chooseShorColumn (j : Fin c) : (Fin g × Fin q) × Fin c → Bool :=
  fun b => decide (b.2 = j)

/-- Sites at one cell coordinate in a fixed column, in all groups. -/
noncomputable def shorColumnCycleUnion (j : Fin c) (p : Cell q h) :
    Finset (Fin (ShorSites g q h c)) :=
  (Finset.univ : Finset (Fin g)).biUnion (fun i => (shorCycle i j p).sites)

theorem mark_shorColumnCycleUnion (j : Fin c) (p : Cell q h) :
    mark (shorColumnCycleUnion (g := g) j p) =
      liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) (mark {p}) := by
  funext x
  rw [show mark (shorColumnCycleUnion (g := g) j p) x =
    if x ∈ shorColumnCycleUnion (g := g) j p then 1 else 0 from rfl]
  have hm : (x ∈ shorColumnCycleUnion (g := g) j p) ↔
      ((shorCellLayout g q h c) x).1.2 = j ∧ ((shorCellLayout g q h c) x).2 = p :=
    mem_shorColumnCycleUnion j p x
  by_cases hc : ((shorCellLayout g q h c) x).1.2 = j
  · by_cases hp : ((shorCellLayout g q h c) x).2 = p
    · rw [ite_eq_left (hm.mpr ⟨hc, hp⟩)]
      simp [liftCellWord, chooseShorColumn, mark, hc, hp]
    · rw [ite_eq_right (fun hm' => hp (hm.mp hm').2)]
      simp [liftCellWord, chooseShorColumn, mark, hc, hp]
  · rw [ite_eq_right (fun hm' => hc (hm.mp hm').1)]
    simp [liftCellWord, chooseShorColumn, mark, hc]

/-- The selected all-ones mask is the physical full-column logical X mask. -/
theorem liftCellWord_fullXColumn (j : Fin c) :
    liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) 1 =
      fun x => fullXColumn (rows := ShorRows g q h) j
        (shorSiteEquiv (ShorRows g q h) c x) := by
  funext x
  have hcol : ((shorCellLayout g q h c) x).1.2 =
      (shorSiteEquiv (ShorRows g q h) c x).2 := rfl
  simp only [liftCellWord, chooseShorColumn, hcol, Pi.one_apply, fullXColumn, decide_eq_true_eq]

#print axioms mark_shorColumnCycleUnion
#print axioms liftCellWord_fullXColumn


theorem shorWordLinearEquiv_liftCellWord_fullXColumn (j : Fin c) :
    shorWordLinearEquiv (ShorRows g q h) c
      (liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) 1) =
    fullXColumn (rows := ShorRows g q h) j := by
  rw [liftCellWord_fullXColumn]
  funext ij
  change fullXColumn j ((shorSiteEquiv (ShorRows g q h) c)
      ((shorSiteEquiv (ShorRows g q h) c).symm ij)) = fullXColumn j ij
  rw [Equiv.apply_symm_apply]

theorem IndexedCellSchedule.column_partition {seed : Cell q h}
    (S : IndexedCellSchedule q h seed) (j : Fin c) :
    shorWordLinearEquiv (ShorRows g q h) c
      (liftCellWord (shorCellLayout g q h c) (chooseShorColumn j)
        (mark (Finset.univ.erase S.pivot)) +
       liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) (mark {S.pivot})) =
    fullXColumn (rows := ShorRows g q h) j := by
  rw [S.lifted_selected_partition]
  exact shorWordLinearEquiv_liftCellWord_fullXColumn j

/-- Reassociate the row index into a cell number and its local coordinate. -/
def groupedRowCellLayout (g q h : ℕ) :
    Fin (ShorRows g q h) ≃ (Fin g × Fin q) × Cell q h :=
  (groupedRowEquiv g q h).trans (Equiv.prodAssoc _ _ _).symm

/-- Identical local parent assignments give the same linear row map in each column. -/
theorem CellParent.liftCells_shorColumn (P : CellParent (cellSize q h) q) :
    (P.liftCells (shorCellLayout g q h c)).run =
      acrossColumnsPhysicalLinearEquiv (columns := c)
        (P.liftCells (groupedRowCellLayout g q h)).run := by
  apply eq_acrossColumnsPhysicalLinearEquiv
  intro x i j
  let e := groupedRowCellLayout g q h
  let u := shorSiteEquiv (ShorRows g q h) c
  let E := shorCellLayout g q h c
  obtain ⟨⟨b, k⟩, rfl⟩ := e.symm.surjective i
  have hsite (a : Cell q h) : E.symm (((b.1, b.2), j), a) =
      u.symm (e.symm (b, a), j) := by
    rcases b with ⟨l, d⟩
    rfl
  change (P.liftCells E).run x (u.symm (e.symm (b, k), j)) =
    (P.liftCells e).run (fun z => x (u.symm (z, j))) (e.symm (b, k))
  rw [← hsite k, P.liftCells_run, P.liftCells_run]
  have hf : (fun a => x (E.symm (((b.1, b.2), j), a))) =
      fun a => x (u.symm (e.symm (b, a), j)) := by
    funext a
    rw [hsite a]
  rw [hf]

#print axioms IndexedCellSchedule.column_partition
#print axioms CellParent.liftCells_shorColumn

end CriticalDepth.FaultShorSaturation
