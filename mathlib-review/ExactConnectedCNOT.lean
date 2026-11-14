import ExactGraphCNOTRouting

/-!
# Exact CNOT on any pair of sites of a connected logical graph
-/

namespace CriticalDepth.Manuscript20261114

open Relation CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary
open CriticalDepth.FaultShorSaturation

noncomputable section

variable {k : ℕ}

/-- A finite word of graph-edge SWAPs routes the control and target of an
edge CNOT to any distinct ordered pair. The inverse routing uses the
adjoint of the same word. -/
theorem exists_routed_CNOT_of_connected
    (E : Fin k → Fin k → Prop) (hConn : ∀ i j, ReflTransGen E i j)
    (a b : Fin k) (hab : a ≠ b) (hEdge : E a b)
    (c t : Fin k) (hct : c ≠ t) :
    ∃ L : List (Fin k × Fin k),
      (∀ e ∈ L, E e.1 e.2) ∧
      let M := (L.map fun e => basisPermutation
        (permuteSites (α := Fin 2) (Equiv.swap e.1 e.2))).prod
      M * edgeOperator a b hab pairCNOT * M.conjTranspose = basisPermutation (cnotWord c t hct) := by
  let p := Equiv.swap a c
  let b' := p b
  let r := Equiv.swap b' t
  have hp : p a = c := Equiv.swap_apply_left a c
  have hbc : b' ≠ c := fun he => hab (p.injective (hp.trans he.symm))
  have hr : r c = c := Equiv.swap_apply_of_ne_of_ne hbc.symm hct
  have ht : r b' = t := Equiv.swap_apply_left b' t
  obtain ⟨L, hL, heL⟩ := exists_edgeSwapWord_of_path (hConn a c)
  obtain ⟨R, hR, heR⟩ := exists_edgeSwapWord_of_path (hConn b' t)
  refine ⟨R ++ L, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hR e he
    · exact hL e he
  · dsimp only
    rw [edgeSwapWord_physical, edgeSwapWord_append, heR, heL]
    change basisPermutation (permuteSites (r * p)) * edgeOperator a b hab pairCNOT *
      (basisPermutation (permuteSites (r * p))).conjTranspose = _
    rw [edgeOperator_cnotWord, basisPermutation_conjTranspose]
    change basisPermutation (permuteSites (r * p)) * basisPermutation (cnotWord a b hab) *
      basisPermutation ((permuteSites (r * p))⁻¹) = _
    rw [basisPermutation_cnotWord_conjugate]
    have ha : (r * p) a = c := (congrArg r hp).trans hr
    have hb : (r * p) b = t := ht
    congr 1
    simp only [ha, hb]

#print axioms exists_routed_CNOT_of_connected

end

end CriticalDepth.Manuscript20261114
