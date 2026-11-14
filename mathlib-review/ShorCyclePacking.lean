import ShorNativeSitePermutation
import ShorNativeParentLayer
import FaultHistoryNormalization

/-!
# Cross-cell cycle gate packing

Each cycle is one supported native gate. Cycles may run in the same
layer as disjoint controlled additions when their sites are idle in
the parent map.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript
open CriticalDepth.FaultHistoryNormalization

variable {n q : ℕ}

structure SiteCycleBlock (n q : ℕ) where
  sites : Finset (Fin n)
  size : sites.card = q
  order : Fin q ≃ sites

def SiteCycleBlock.perm (B : SiteCycleBlock n q) : Equiv.Perm B.sites :=
  (B.order.symm.trans (finRotate q)).trans B.order

def SiteCycleBlock.gate (B : SiteCycleBlock n q) : ListGate n (fun _ => 2) q :=
  sitePermutationGate B.sites B.perm B.size.le

@[simp] theorem SiteCycleBlock.gate_support (B : SiteCycleBlock n q) :
    B.gate.support = B.sites := rfl

def SiteCycleBlock.run {α : Type*} (B : SiteCycleBlock n q) : Equiv.Perm (Fin n → α) :=
  permuteSites (Equiv.Perm.ofSubtype B.perm)

theorem SiteCycleBlock.run_on_site {α : Type*} (B : SiteCycleBlock n q)
    (v : Fin n → α) (j : Fin q) :
    B.run v (B.order j).val = v (B.order ((finRotate q).symm j)).val := by
  have hs : (Equiv.Perm.ofSubtype B.perm).symm = Equiv.Perm.ofSubtype B.perm.symm := by
    change (Equiv.Perm.ofSubtype B.perm)⁻¹ = Equiv.Perm.ofSubtype B.perm⁻¹
    rw [map_inv]
  change v ((Equiv.Perm.ofSubtype B.perm).symm (B.order j).val) = _
  rw [hs, Equiv.Perm.ofSubtype_apply_coe]
  simp [SiteCycleBlock.perm]

theorem SiteCycleBlock.run_off_site {α : Type*} (B : SiteCycleBlock n q)
    (v : Fin n → α) (i : Fin n) (hi : i ∉ B.sites) :
    B.run v i = v i := by
  have hs : (Equiv.Perm.ofSubtype B.perm).symm = Equiv.Perm.ofSubtype B.perm.symm := by
    change (Equiv.Perm.ofSubtype B.perm)⁻¹ = Equiv.Perm.ofSubtype B.perm⁻¹
    rw [map_inv]
  change v ((Equiv.Perm.ofSubtype B.perm).symm i) = v i
  rw [hs, Equiv.Perm.ofSubtype_apply_of_not_mem B.perm.symm hi]

theorem SiteCycleBlock.run_fixes_uniform (B : SiteCycleBlock n q)
    (v : Fin n → Bit) (a : Bit) (ha : ∀ i ∈ B.sites, v i = a) :
    B.run v = v := by
  funext i
  by_cases hi : i ∈ B.sites
  · let j := B.order.symm ⟨i, hi⟩
    have he : (B.order j).val = i := congrArg Subtype.val (B.order.apply_symm_apply ⟨i, hi⟩)
    rw [← he, B.run_on_site, ha _ (B.order _).property, ha _ (B.order _).property]
  · exact B.run_off_site v i hi

theorem nativeParentLayer_support_avoids_idle
    (p : Fin n → Option (Fin n)) (hp : ∀ i a, p i = some a → p a = none)
    (hcard : ∀ a, (parentSites p a).card ≤ q)
    (i : Fin n) (hi : p i = none) (hsource : ∀ k, p k ≠ some i) :
    ∀ G ∈ (nativeParentLayer p hp hcard).gates, i ∉ G.support := by
  intro G hg
  change G ∈ (parentBlocks p hcard).map (fun B => blockFanoutGate B.sites B.pivot B.arity) at hg
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hg
  unfold parentBlocks at hB
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hB
  have hactive : (targetSites p a).Nonempty := (Finset.mem_filter.mp (Finset.mem_toList.mp ha)).2
  change i ∉ parentSites p a
  intro hm
  rcases (parentSites_mem p i a).mp hm with rfl | h
  · obtain ⟨k, hk⟩ := hactive
    exact hsource k (Finset.mem_filter.mp hk).2
  · rw [hi] at h
    cases h

/-- Pack the seed or pivot cycles together with that step's disjoint fanout. -/
noncomputable def cycleAndParentLayer
    (blocks : List (SiteCycleBlock n q))
    (hdis : blocks.Pairwise fun A B => Disjoint A.sites B.sites)
    (p : Fin n → Option (Fin n)) (hp : ∀ i a, p i = some a → p a = none)
    (hcard : ∀ a, (parentSites p a).card ≤ q)
    (hidle : ∀ B ∈ blocks, ∀ i ∈ B.sites, p i = none ∧ ∀ k, p k ≠ some i) :
    ArbitraryLayer n (fun _ => 2) q where
  gates := blocks.map SiteCycleBlock.gate ++ (nativeParentLayer p hp hcard).gates
  disjoint := by
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr hdis, (nativeParentLayer p hp hcard).disjoint, ?_⟩
    intro G hG H hH
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hG
    exact Finset.disjoint_left.mpr fun i hi hj =>
      (nativeParentLayer_support_avoids_idle p hp hcard i (hidle B hB i hi).1
        (hidle B hB i hi).2 H hH) hj

theorem cycleAndParentLayer_eval
    (blocks : List (SiteCycleBlock n q))
    (hdis : blocks.Pairwise fun A B => Disjoint A.sites B.sites)
    (p : Fin n → Option (Fin n)) (hp : ∀ i a, p i = some a → p a = none)
    (hcard : ∀ a, (parentSites p a).card ≤ q)
    (hidle : ∀ B ∈ blocks, ∀ i ∈ B.sites, p i = none ∧ ∀ k, p k ≠ some i) :
    (cycleAndParentLayer blocks hdis p hp hcard hidle).eval =
      (nativeParentLayer p hp hcard).eval * listGateEval (blocks.map SiteCycleBlock.gate) := by
  change listGateEval (_ ++ _) = _
  simp [listGateEval, ArbitraryLayer.eval, List.reverse_append, List.prod_append]

/-- An original nonempty gate has a native slot on the same sites after
normalizing a layer. -/
theorem ArbitraryLayer.exists_normalized_support
    (L : ArbitraryLayer n (fun _ => 2) q)
    (G : ListGate n (fun _ => 2) q) (hG : G ∈ L.gates) (hne : G.support.Nonempty) :
    ∃ j : Fin n, L.normalized.support j = G.support := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hG
  let k : {l : Fin L.gates.length // (L.gates.get l).support.Nonempty} :=
    ⟨i, by rwa [hi]⟩
  exact ⟨(layerLocationEquiv L k).val, (layerLocationEquiv_support L k).trans
    (congrArg ListGate.support hi)⟩

#print axioms cycleAndParentLayer
#print axioms ArbitraryLayer.exists_normalized_support

end CriticalDepth.FaultShorSaturation