import ShorNativeParallelFanout

/-!
# Realizing a bounded parent map in one native layer

A parent map in which pivots are untouched partitions the working sites
into disjoint fanout blocks indexed by their pivots.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript

open scoped BigOperators

variable {n q : ℕ}

def targetSites (parent : Fin n → Option (Fin n)) (a : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => parent i = some a

def parentSites (parent : Fin n → Option (Fin n)) (a : Fin n) : Finset (Fin n) :=
  insert a (targetSites parent a)

theorem parentSites_mem (parent : Fin n → Option (Fin n)) (i a : Fin n) :
    i ∈ parentSites parent a ↔ i = a ∨ parent i = some a := by
  simp [parentSites, targetSites]

private theorem parentSites_disjoint (parent : Fin n → Option (Fin n))
    (huntouched : ∀ i a, parent i = some a → parent a = none)
    (a b : Fin n) (ha : (targetSites parent a).Nonempty)
    (hb : (targetSites parent b).Nonempty) (hab : a ≠ b) :
    Disjoint (parentSites parent a) (parentSites parent b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hp (s t : Fin n) (h : s ∈ targetSites parent t) : parent s = some t :=
    (Finset.mem_filter.mp h).2
  have hna := huntouched i a (hp i a hi)
  have hnb := huntouched j b (hp j b hj)
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  rcases (parentSites_mem parent x a).mp hxa with rfl | hxa <;>
    rcases (parentSites_mem parent _ b).mp hxb with hab' | hxb
  · exact hab hab'
  · rw [hna] at hxb
    cases hxb
  · rw [hab', hnb] at hxa
    cases hxa
  · exact hab (Option.some.inj (hxa.symm.trans hxb))

noncomputable def parentBlocks (parent : Fin n → Option (Fin n))
    (hcard : ∀ a, (parentSites parent a).card ≤ q) : List (FanoutBlock n q) :=
  ((Finset.univ.filter fun a => (targetSites parent a).Nonempty).toList).map fun a =>
    ⟨parentSites parent a, ⟨a, (parentSites_mem parent a a).mpr (.inl rfl)⟩, hcard a⟩

theorem parentBlocks_pairwise (parent : Fin n → Option (Fin n))
    (huntouched : ∀ i a, parent i = some a → parent a = none)
    (hcard : ∀ a, (parentSites parent a).card ≤ q) :
    (parentBlocks parent hcard).Pairwise fun A B => Disjoint A.sites B.sites := by
  classical
  unfold parentBlocks
  rw [List.pairwise_map]
  let L : List (Fin n) := (Finset.univ.filter fun a => (targetSites parent a).Nonempty).toList
  have hl : L.Nodup := Finset.nodup_toList _
  refine hl.imp_of_mem ?_
  intro a b ha hb hab
  have active (c : Fin n) (hc : c ∈ L) : (targetSites parent c).Nonempty :=
    (Finset.mem_filter.mp (Finset.mem_toList.mp hc)).2
  exact parentSites_disjoint parent huntouched a b (active a ha) (active b hb) hab

/-- Every simultaneous bounded fanout admits a physical layer of the
advertised arity. Its block family omits pivots with no targets. -/
noncomputable def nativeParentLayer (parent : Fin n → Option (Fin n))
    (huntouched : ∀ i a, parent i = some a → parent a = none)
    (hcard : ∀ a, (parentSites parent a).card ≤ q) : ArbitraryLayer n (fun _ => 2) q :=
  fanoutLayerOfBlocks (parentBlocks parent hcard) (parentBlocks_pairwise parent huntouched hcard)

#print axioms parentBlocks_pairwise
#print axioms nativeParentLayer

end CriticalDepth.FaultShorSaturation