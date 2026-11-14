import ShorCyclePacking
import FaultShorScheduleIteration

/-!
# Rectangular layout of the Shor cycle gates

Rows decompose into groups, cells and sites. Each cycle uses the
same marked site of each cell in one group and one column.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript

abbrev ShorRows (g q h : ℕ) := g * (q * cellSize q h)

def groupedRowEquiv (g q h : ℕ) :
    Fin (ShorRows g q h) ≃ Fin g × (Fin q × Cell q h) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

abbrev ShorSites (g q h columns : ℕ) := ShorRows g q h * columns

def shorCellLayout (g q h columns : ℕ) :
    Fin (ShorSites g q h columns) ≃
      ((Fin g × Fin q) × Fin columns) × Cell q h :=
  (shorSiteEquiv (ShorRows g q h) columns).trans
    ((Equiv.prodCongr (groupedRowEquiv g q h) (Equiv.refl _)).trans
      { toFun := fun x => (((x.1.1, x.1.2.1), x.2), x.1.2.2)
        invFun := fun x => ((x.1.1.1, (x.1.1.2, x.2)), x.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })

variable {g q h c : ℕ}

def numberedCycleSites (i : Fin g) (j : Fin c) (p : Cell q h) :
    Fin q ↪ Fin (ShorSites g q h c) where
  toFun cell := (shorCellLayout g q h c).symm (((i, cell), j), p)
  inj' := by
    intro a b hab
    have h := congrArg (fun x => ((shorCellLayout g q h c) x).1.1.2) hab
    simpa using h

noncomputable def shorCycle (i : Fin g) (j : Fin c) (p : Cell q h) :
    SiteCycleBlock (ShorSites g q h c) q where
  sites := Finset.univ.map (numberedCycleSites i j p)
  size := by simp
  order := Equiv.ofBijective
    (fun s => ⟨numberedCycleSites i j p s, Finset.mem_map.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun x y h => (numberedCycleSites i j p).injective (congrArg Subtype.val h),
      fun k => by
        obtain ⟨x, _, hx⟩ := Finset.mem_map.mp k.property
        exact ⟨x, Subtype.ext hx⟩⟩

theorem shorCycle_apply_order (i : Fin g) (j : Fin c) (p : Cell q h) (a : Fin q) :
    ((shorCycle i j p).order a).val = (shorCellLayout g q h c).symm (((i, a), j), p) := rfl

theorem mem_shorCycle_sites (i : Fin g) (j : Fin c) (p : Cell q h)
    (x : Fin (ShorSites g q h c)) :
    x ∈ (shorCycle i j p).sites ↔
      ((shorCellLayout g q h c) x).1.1.1 = i ∧
      ((shorCellLayout g q h c) x).1.2 = j ∧
      ((shorCellLayout g q h c) x).2 = p := by
  constructor
  · intro hx
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx
    rw [← ha]
    have he : (shorCellLayout g q h c) (numberedCycleSites i j p a) = (((i, a), j), p) :=
      (shorCellLayout g q h c).apply_symm_apply _
    rw [he]
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hi, hj, hp⟩
    apply Finset.mem_map.mpr
    refine ⟨((shorCellLayout g q h c) x).1.1.2, Finset.mem_univ _, ?_⟩
    apply (shorCellLayout g q h c).injective
    change (shorCellLayout g q h c) ((shorCellLayout g q h c).symm
      (((i, ((shorCellLayout g q h c) x).1.1.2), j), p)) = _
    rw [Equiv.apply_symm_apply, ← hi, ← hj, ← hp]

theorem shorCycle_sites_disjoint (p : Cell q h) {a b : Fin g × Fin c} (hneq : a ≠ b) :
    Disjoint (shorCycle a.1 a.2 p).sites (shorCycle b.1 b.2 p).sites := by
  apply Finset.disjoint_left.mpr
  intro x ha hb
  obtain ⟨hai, haj, _⟩ := (mem_shorCycle_sites _ _ _ _).mp ha
  obtain ⟨hbi, hbj, _⟩ := (mem_shorCycle_sites _ _ _ _).mp hb
  exact hneq (Prod.ext (hai.symm.trans hbi) (haj.symm.trans hbj))

noncomputable def shorCycleBlocks (g q h c : ℕ) (p : Cell q h) :
    List (SiteCycleBlock (ShorSites g q h c) q) :=
  (Finset.univ : Finset (Fin g × Fin c)).toList.map fun ij => shorCycle ij.1 ij.2 p

theorem shorCycleBlocks_pairwise (p : Cell q h) :
    (shorCycleBlocks g q h c p).Pairwise fun A B => Disjoint A.sites B.sites := by
  unfold shorCycleBlocks
  rw [List.pairwise_map]
  apply (Finset.nodup_toList (Finset.univ : Finset (Fin g × Fin c))).imp
  exact fun hneq => shorCycle_sites_disjoint p hneq

theorem shorCycle_mem_blocks (i : Fin g) (j : Fin c) (p : Cell q h) :
    shorCycle i j p ∈ shorCycleBlocks g q h c p :=
  List.mem_map.mpr ⟨(i, j), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

theorem shorCycle_nonempty (i : Fin g) (j : Fin c) (p : Cell q h) (hq : 0 < q) :
    (shorCycle i j p).sites.Nonempty :=
  ⟨((shorCycle i j p).order ⟨0, hq⟩).val, ((shorCycle i j p).order ⟨0, hq⟩).property⟩

theorem mem_shorColumnCycleUnion (j : Fin c) (p : Cell q h)
    (x : Fin (ShorSites g q h c)) :
    x ∈ (Finset.univ : Finset (Fin g)).biUnion (fun i => (shorCycle i j p).sites) ↔
      ((shorCellLayout g q h c) x).1.2 = j ∧ ((shorCellLayout g q h c) x).2 = p := by
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (mem_shorCycle_sites i j p x).mp hi |>.2
  · intro hx
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _,
      (mem_shorCycle_sites ((shorCellLayout g q h c) x).1.1.1 j p x).mpr ⟨rfl, hx⟩⟩

#print axioms shorCycleBlocks_pairwise
#print axioms mem_shorColumnCycleUnion

end CriticalDepth.FaultShorSaturation