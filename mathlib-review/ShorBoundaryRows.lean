import ShorBoundaryCircuit
import ShorIndexedScheduleColumn

/-!
# Identical boundary action in every column

The common row action is read directly from the group index, the cell
index, and the marked cell coordinate.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

variable {g q h c : ℕ}

def cycleRowAt (p : Cell q h) (a : Fin (ShorRows g q h)) :
    Fin (ShorRows g q h) :=
  let e := groupedRowEquiv g q h
  let z := e a
  if z.2.2 = p then e.symm (z.1, ((finRotate q).symm z.2.1, p)) else a

theorem shorCycles_action (p : Cell q h) (x : Fin (ShorSites g q h c) → Bit)
    (a : Fin (ShorRows g q h)) (j : Fin c) :
    siteCyclesLinearEquiv (shorCycleBlocks g q h c p) x
        ((shorSiteEquiv (ShorRows g q h) c).symm (a, j)) =
      x ((shorSiteEquiv (ShorRows g q h) c).symm (cycleRowAt p a, j)) := by
  let e := groupedRowEquiv g q h
  let u := shorSiteEquiv (ShorRows g q h) c
  let E := shorCellLayout g q h c
  let B := shorCycle (e a).1 j p
  change siteCyclesWordEquiv _ _ _ = _
  rw [siteCyclesWordEquiv_apply]
  have hE : E (u.symm (a, j)) = ((((e a).1, (e a).2.1), j), (e a).2.2) := by
    change (shorCellLayout g q h c) (u.symm (a, j)) = _
    simp [shorCellLayout, e, u]
  by_cases hp : (e a).2.2 = p
  · have orderE (k : Fin q) : (B.order k).val = u.symm (e.symm ((e a).1, (k, p)), j) := by
      rw [show (B.order k).val = E.symm ((((e a).1, k), j), p) from shorCycle_apply_order _ _ _ _]
      apply E.injective
      simp [E, u, e, shorCellLayout]
    have hsite : (B.order (e a).2.1).val = u.symm (a, j) := by
      rw [orderE]
      congr 2
      apply e.injective
      rw [e.apply_symm_apply]
      exact Prod.ext rfl (Prod.ext rfl hp.symm)
    rw [← hsite, runSiteCycles_on_site _ (shorCycleBlocks_pairwise p) _ B
      (shorCycle_mem_blocks _ _ _)]
    rw [orderE]
    have hp' : (groupedRowEquiv g q h a).2.2 = p := hp
    simp only [cycleRowAt, hp', ite_true]
    rfl
  · rw [runSiteCycles_off_sites]
    · have hp' : (groupedRowEquiv g q h a).2.2 ≠ p := hp
      simp only [cycleRowAt, hp', ite_false]
    · intro C hC hm
      unfold shorCycleBlocks at hC
      obtain ⟨ij, _, rfl⟩ := List.mem_map.mp hC
      have ht := ((mem_shorCycle_sites ij.1 ij.2 p (u.symm (a, j))).mp hm).2.2
      change (E (u.symm (a, j))).2 = p at ht
      rw [hE] at ht
      exact hp ht

theorem exists_shorCycles_row (p : Cell q h) (j₀ : Fin c) :
    ∃ T : (Fin (ShorRows g q h) → Bit) ≃ₗ[Bit] (Fin (ShorRows g q h) → Bit),
      siteCyclesLinearEquiv (shorCycleBlocks g q h c p) =
        acrossColumnsPhysicalLinearEquiv (columns := c) T := by
  obtain ⟨T, _, hT⟩ := exists_acrossColumnsPhysicalLinearEquiv_of_action
    (siteCyclesLinearEquiv (shorCycleBlocks g q h c p))
    (fun z i => z (cycleRowAt p i)) j₀ (shorCycles_action p)
  exact ⟨T, hT⟩

theorem acrossColumnsPhysical_trans {rows columns : ℕ}
    (T U : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) :
    (acrossColumnsPhysicalLinearEquiv (columns := columns) T).trans
        (acrossColumnsPhysicalLinearEquiv (columns := columns) U) =
      acrossColumnsPhysicalLinearEquiv (columns := columns) (T.trans U) := by
  apply eq_acrossColumnsPhysicalLinearEquiv
  intro x i j
  change acrossColumnsPhysicalLinearEquiv (columns := columns) U
      (acrossColumnsPhysicalLinearEquiv (columns := columns) T x) _ = _
  rw [acrossColumnsPhysicalLinearEquiv_apply]
  have hc : (fun k => acrossColumnsPhysicalLinearEquiv (columns := columns) T x
      ((shorSiteEquiv rows columns).symm (k, j))) =
      T (fun k => x ((shorSiteEquiv rows columns).symm (k, j))) :=
    funext fun k => acrossColumnsPhysicalLinearEquiv_apply T x k j
  rw [hc]
  rfl

theorem exists_shorBoundaryRun_row (P : CellParent (cellSize q h) q)
    (p : Cell q h) (j₀ : Fin c) :
    ∃ T : (Fin (ShorRows g q h) → Bit) ≃ₗ[Bit] (Fin (ShorRows g q h) → Bit),
      shorBoundaryRun (g := g) (c := c) P p =
        acrossColumnsPhysicalLinearEquiv (columns := c) T := by
  obtain ⟨T, hT⟩ := exists_shorCycles_row (g := g) p j₀
  refine ⟨T.trans ((P.liftCells (groupedRowCellLayout g q h)).run), ?_⟩
  rw [shorBoundaryRun, hT, CellParent.liftCells_shorColumn, acrossColumnsPhysical_trans]

#print axioms exists_shorBoundaryRun_row

end CriticalDepth.FaultShorSaturation