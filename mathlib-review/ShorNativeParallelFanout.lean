import ShorNativeFanout

/-!
# Simultaneous disjoint fanout blocks

Each block is one native gate and the whole list is one parallel layer.
Its binary action on each block is exactly that block's fanout map.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript

variable {n q : ℕ}

/-- The sites, chosen pivot, and arity bound of one fanout gate. -/
structure FanoutBlock (n q : ℕ) where
  sites : Finset (Fin n)
  pivot : sites
  arity : sites.card ≤ q

def FanoutBlock.run (B : FanoutBlock n q) (word : Fin n → Bit) : Fin n → Bit :=
  blockFanoutEquiv B.sites B.pivot.val word

def fanoutLayerOfBlocks (blocks : List (FanoutBlock n q))
    (hdis : blocks.Pairwise fun A B => Disjoint A.sites B.sites) :
    ArbitraryLayer n (fun _ => 2) q where
  gates := blocks.map fun B => blockFanoutGate B.sites B.pivot B.arity
  disjoint := by
    rw [List.pairwise_map]
    exact hdis

private theorem applyBlocks_outside (blocks : List (FanoutBlock n q))
    (word : Fin n → Bit) (i : Fin n)
    (hout : ∀ B ∈ blocks, i ∉ B.sites) :
    blocks.foldl (fun x B => B.run x) word i = word i := by
  induction blocks generalizing word with
  | nil => rfl
  | cons B rest ih =>
    change rest.foldl (fun x T => T.run x) (B.run word) i = word i
    rw [ih (B.run word) (fun T hm => hout T (List.mem_cons_of_mem B hm))]
    exact blockFanout_fixes_outside B.sites B.pivot word i (hout B (by simp))

theorem applyBlocks_on_block (blocks : List (FanoutBlock n q))
    (hdis : blocks.Pairwise fun A B => Disjoint A.sites B.sites)
    (word : Fin n → Bit) (B : FanoutBlock n q)
    (hB : B ∈ blocks) (i : Fin n) (hi : i ∈ B.sites) :
    blocks.foldl (fun x T => T.run x) word i = B.run word i := by
  induction blocks generalizing word with
  | nil => simp at hB
  | cons first rest ih =>
    obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hdis
    change rest.foldl (fun x T => T.run x) (first.run word) i = B.run word i
    rcases List.mem_cons.mp hB with h | hm
    · subst first
      exact applyBlocks_outside rest (B.run word) i
        (fun T ht => Finset.disjoint_left.mp (hfirst _ ht) hi)
    · rw [ih hrest (first.run word) hm]
      have hdis := Finset.disjoint_left.mp (hfirst _ hm)
      have hnot (j : Fin n) (hj : j ∈ B.sites) : j ∉ first.sites :=
        fun h => hdis h hj
      have hi' := blockFanout_fixes_outside first.sites first.pivot word i (hnot i hi)
      have hp' := blockFanout_fixes_outside first.sites first.pivot word B.pivot.val
        (hnot B.pivot.val B.pivot.property)
      unfold FanoutBlock.run
      rw [blockFanoutEquiv_apply B.sites, blockFanoutEquiv_apply B.sites, hi', hp']

#print axioms fanoutLayerOfBlocks
#print axioms applyBlocks_on_block

end CriticalDepth.FaultShorSaturation