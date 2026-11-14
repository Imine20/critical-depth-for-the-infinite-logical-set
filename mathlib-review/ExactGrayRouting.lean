import CriticalDepthMathlib
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Gray routing of an arbitrary pair of computational basis states
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript SimpleGraph

variable {k : ℕ}

/-- Two basis strings are adjacent when they differ at exactly one site. -/
def GrayAdjacent (x y : QubitBasis k) : Prop :=
  ∃ i : Fin k, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j

def grayGraph (k : ℕ) : SimpleGraph (QubitBasis k) where
  Adj := GrayAdjacent
  symm := ⟨fun _ _ ⟨i, h, he⟩ => ⟨i, h.symm, fun j hj => (he j hj).symm⟩⟩
  loopless := ⟨fun _ ⟨_, h, _⟩ => h rfl⟩

/-- Change one differing coordinate at a time to get a Gray walk. -/
theorem grayGraph_reachable (x y : QubitBasis k) : (grayGraph k).Reachable x y := by
  classical
  let disagreements (v : QubitBasis k) := Finset.univ.filter fun i => v i ≠ y i
  generalize hm : (disagreements x).card = m
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    by_cases he : x = y
    · subst x
      exact SimpleGraph.Reachable.refl _
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp he
      let z : QubitBasis k := Function.update x i (y i)
      have hAdj : (grayGraph k).Adj x z := by
        refine ⟨i, by simpa [z] using hi, ?_⟩
        intro j hj
        simp [z, Function.update_of_ne hj]
      have hD : disagreements z = (disagreements x).erase i := by
        ext j
        by_cases hj : j = i
        · subst j; simp [disagreements, z]
        · simp [disagreements, z, hj, Function.update_of_ne hj]
      have hLt : (disagreements z).card < m := by
        rw [hD, ← hm]
        apply Finset.card_erase_lt_of_mem
        simp [disagreements, hi]
      exact hAdj.reachable.trans (ih _ hLt z rfl)

/-- Every pair of basis states admits a simple Gray path. -/
theorem grayGraph_has_path (x y : QubitBasis k) : Nonempty ((grayGraph k).Path x y) := by
  obtain ⟨w⟩ := grayGraph_reachable x y
  exact ⟨w.toPath⟩

/-- Execution order of the adjacent transpositions that move the far
endpoint toward the starting endpoint of a walk. -/
def grayPathSwaps {x y : QubitBasis k} : (grayGraph k).Walk x y →
    List (QubitBasis k × QubitBasis k)
  | .nil => []
  | @SimpleGraph.Walk.cons _ _ x z _ _ p => grayPathSwaps p ++ [(z, x)]

def executeGraySwaps (L : List (QubitBasis k × QubitBasis k))
    (x : QubitBasis k) : QubitBasis k :=
  L.foldl (fun z pair => Equiv.swap pair.1 pair.2 z) x

private theorem grayPathSwaps_neighbor {x y : QubitBasis k} (p : (grayGraph k).Walk x y) :
    ∀ a ∈ grayPathSwaps p, GrayAdjacent a.1 a.2 := by
  induction p with
  | nil => simp [grayPathSwaps]
  | cons h p ih =>
    intro a ha
    rw [grayPathSwaps, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ih a ha
    · exact h.symm

private theorem grayPathSwaps_fixes_off_support {x y : QubitBasis k}
    (p : (grayGraph k).Walk x y) (z : QubitBasis k) (hz : z ∉ p.support) :
    executeGraySwaps (grayPathSwaps p) z = z := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hz
    unfold executeGraySwaps
    rw [grayPathSwaps, List.foldl_append]
    change Equiv.swap v u (executeGraySwaps (grayPathSwaps p) z) = z
    rw [ih hz.2]
    exact Equiv.swap_apply_of_ne_of_ne
      (fun he => hz.2 (he.symm ▸ p.start_mem_support)) hz.1

private theorem grayPathSwaps_moves_end {x y : QubitBasis k} (p : (grayGraph k).Walk x y) :
    executeGraySwaps (grayPathSwaps p) y = x := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    unfold executeGraySwaps
    rw [grayPathSwaps, List.foldl_append]
    change Equiv.swap v u (executeGraySwaps (grayPathSwaps p) w) = u
    rw [ih, Equiv.swap_apply_left]

/-- The permutation which executes the listed swaps from left to right. -/
def graySwapPermutation (L : List (QubitBasis k × QubitBasis k)) :
    Equiv.Perm (QubitBasis k) :=
  L.foldr (fun pair tail => (Equiv.swap pair.1 pair.2).trans tail) (Equiv.refl _)

theorem graySwapPermutation_apply (L : List (QubitBasis k × QubitBasis k))
    (x : QubitBasis k) : graySwapPermutation L x = executeGraySwaps L x := by
  induction L generalizing x with
  | nil => rfl
  | cons p tail ih =>
    change graySwapPermutation tail (Equiv.swap p.1 p.2 x) =
      executeGraySwaps tail (Equiv.swap p.1 p.2 x)
    exact ih _

/-- Omit the first edge of a simple Gray path. The remaining edge swaps
fix x and send y to its neighbor z, using only one-bit transpositions. -/
theorem gray_routing_swaps {x y : QubitBasis k} (hxy : x ≠ y) :
    ∃ (z : QubitBasis k) (L : List (QubitBasis k × QubitBasis k)), GrayAdjacent x z ∧
      (∀ a ∈ L, GrayAdjacent a.1 a.2) ∧
      executeGraySwaps L x = x ∧ executeGraySwaps L y = z := by
  obtain ⟨⟨p, hp⟩⟩ := grayGraph_has_path x y
  cases p with
  | nil => exact (hxy rfl).elim
  | @cons _ z _ hadj tail =>
    have hOff : x ∉ tail.support := by
      have h := hp.support_nodup
      rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at h
      exact h.1
    exact ⟨z, grayPathSwaps tail, hadj, grayPathSwaps_neighbor tail,
      grayPathSwaps_fixes_off_support tail x hOff, grayPathSwaps_moves_end tail⟩

#print axioms grayGraph_has_path
#print axioms gray_routing_swaps

end CriticalDepth.Manuscript20261114
