import ExactCZCNOTSwap
import ExactGraphSWAP

/-!
# Embedding two-qubit edge gates in the logical register
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.BinaryPermutationUnitary CriticalDepth.FaultShorSaturation
open Matrix
open scoped Kronecker

noncomputable section

variable {k : ℕ}

/-- The values at two distinct ordered sites identify their local basis
with a product of two one-qubit bases. -/
def edgeBasis (i j : Fin k) (hij : i ≠ j) :
    Fin 2 × Fin 2 ≃ LocalBasis (fun _ => 2) ({i,j} : Finset (Fin k)) where
  toFun b s := if s.val = i then b.1 else b.2
  invFun x := (x ⟨i, by simp⟩, x ⟨j, by simp⟩)
  left_inv b := by simp [Ne.symm hij]
  right_inv x := by
    funext s
    rcases Finset.mem_insert.mp s.property with h | h
    · have hs : s = ⟨i, by simp⟩ := Subtype.ext h
      subst s
      simp
    · have hs : s = ⟨j, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp h)
      subst s
      simp [Ne.symm hij]

/-- Embed a two-qubit matrix while retaining the other coordinates. -/
def edgeOperator (i j : Fin k) (hij : i ≠ j) (A : Operator (Fin 2 × Fin 2)) :
    Operator (QubitBasis k) :=
  localEmbed ({i,j} : Finset (Fin k))
    (Matrix.reindex (edgeBasis i j hij) (edgeBasis i j hij) A)

theorem edgeOperator_apply (i j : Fin k) (hij : i ≠ j)
    (A : Operator (Fin 2 × Fin 2)) (x y : QubitBasis k) :
    edgeOperator i j hij A x y =
      if ∀ s, s ≠ i → s ≠ j → x s = y s
      then A (x i,x j) (y i,y j) else 0 := by
  classical
  have he : (∀ s, s ∉ ({i,j} : Finset (Fin k)) → x s = y s) ↔
      ∀ s, s ≠ i → s ≠ j → x s = y s := by
    simp [or_imp]
  unfold edgeOperator localEmbed
  simp only [he]
  rfl

theorem edgeOperator_mul (i j : Fin k) (hij : i ≠ j)
    (A B : Operator (Fin 2 × Fin 2)) :
    edgeOperator i j hij (A * B) = edgeOperator i j hij A * edgeOperator i j hij B := by
  unfold edgeOperator
  rw [← localEmbed_mul]
  congr 1
  exact map_mul (Matrix.reindexRingEquiv ℂ (edgeBasis i j hij)) A B

theorem edgeOperator_one (i j : Fin k) (hij : i ≠ j) :
    edgeOperator i j hij 1 = 1 := by
  unfold edgeOperator
  rw [← localEmbed_one ({i,j} : Finset (Fin k))]
  congr 1
  exact map_one (Matrix.reindexRingEquiv ℂ (edgeBasis i j hij))

theorem edgeOperator_smul (i j : Fin k) (hij : i ≠ j)
    (z : ℂ) (A : Operator (Fin 2 × Fin 2)) :
    edgeOperator i j hij (z • A) = z • edgeOperator i j hij A := by
  unfold edgeOperator
  rw [← localEmbed_smul]
  congr 1

theorem edgeOperator_add (i j : Fin k) (hij : i ≠ j)
    (A B : Operator (Fin 2 × Fin 2)) :
    edgeOperator i j hij (A + B) = edgeOperator i j hij A + edgeOperator i j hij B := by
  unfold edgeOperator
  rw [← localEmbed_add]
  congr 1

theorem edgeOperator_rotation (i j : Fin k) (hij : i ≠ j)
    (A : Operator (Fin 2 × Fin 2)) (t : ℝ) :
    edgeOperator i j hij (rotation A t) = rotation (edgeOperator i j hij A) t := by
  simp only [rotation, affine, edgeOperator_add, edgeOperator_smul, edgeOperator_one]

/-- Exact CZ as an onsite Z/Z/ZZ word on an arbitrary edge. -/
theorem edgeCZ_eq_Z_Z_ZZ (i j : Fin k) (hij : i ≠ j) :
    edgeOperator i j hij pairCZ = (Circle.exp (Real.pi / 4) : ℂ) •
      (rotation (edgeOperator i j hij pairZLeft) (-Real.pi / 4) *
        rotation (edgeOperator i j hij pairZRight) (-Real.pi / 4) *
        rotation (edgeOperator i j hij pairZLeft * edgeOperator i j hij pairZRight)
          (Real.pi / 4)) := by
  rw [pairCZ_eq_Z_Z_ZZ]
  simp only [edgeOperator_mul, edgeOperator_smul, edgeOperator_rotation]

theorem edgeCNOT_eq_targetHadamard_CZ (i j : Fin k) (hij : i ≠ j) :
    edgeOperator i j hij pairCNOT =
      edgeOperator i j hij ((1 : Operator (Fin 2)) ⊗ₖ pairHadamard) *
        edgeOperator i j hij pairCZ *
        edgeOperator i j hij ((1 : Operator (Fin 2)) ⊗ₖ pairHadamard) := by
  rw [pairCNOT_eq_targetHadamard_CZ]
  simp only [edgeOperator_mul]

theorem edgeSwap_eq_CNOTs (i j : Fin k) (hij : i ≠ j) :
    edgeOperator i j hij pairSwap =
      edgeOperator i j hij pairCNOT * edgeOperator i j hij pairReverseCNOT *
        edgeOperator i j hij pairCNOT := by
  rw [pairSwap_eq_CNOT_reverseCNOT_CNOT]
  simp only [edgeOperator_mul]

/-- The embedded two-qubit swap is the same physical permutation
matrix as the transposition used in the graph edge word. -/
theorem edgeOperator_swap (i j : Fin k) (hij : i ≠ j) :
    edgeOperator i j hij pairSwap = basisPermutation (permuteSites (Equiv.swap i j)) := by
  classical
  ext x y
  rw [edgeOperator_apply, basisPermutation_apply]
  have hi : permuteSites (α := Fin 2) (Equiv.swap i j) y i = y j := by
    change y ((Equiv.swap i j).symm i) = y j
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hj : permuteSites (α := Fin 2) (Equiv.swap i j) y j = y i := by
    change y ((Equiv.swap i j).symm j) = y i
    rw [Equiv.symm_swap, Equiv.swap_apply_right]
  have hout (s : Fin k) (hsi : s ≠ i) (hsj : s ≠ j) :
      permuteSites (α := Fin 2) (Equiv.swap i j) y s = y s := by
    change y ((Equiv.swap i j).symm s) = y s
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hsi hsj]
  have hEq : x = permuteSites (Equiv.swap i j) y ↔
      (∀ s, s ≠ i → s ≠ j → x s = y s) ∧ x i = y j ∧ x j = y i := by
    constructor
    · intro h
      exact ⟨fun s hsi hsj => (congrFun h s).trans (hout s hsi hsj),
        (congrFun h i).trans hi, (congrFun h j).trans hj⟩
    · rintro ⟨ho, hxi, hxj⟩
      funext s
      by_cases hs : s = i
      · subst s
        exact hxi.trans hi.symm
      by_cases hs' : s = j
      · subst s
        exact hxj.trans hj.symm
      exact (ho s hs hs').trans (hout s hs hs').symm
  simp only [hEq]
  by_cases h : ∀ s, s ≠ i → s ≠ j → x s = y s
  · rw [if_pos h]
    have he : ((∀ s, s ≠ i → s ≠ j → x s = y s) ∧ x i = y j ∧ x j = y i) ↔
        (x i = y j ∧ x j = y i) := ⟨fun hx => hx.2, fun hx => ⟨h, hx⟩⟩
    simp only [pairSwap, Prod.swap, Prod.mk.injEq, he]
  · rw [if_neg h]
    simp only [h, false_and, ite_false]

#print axioms edgeCZ_eq_Z_Z_ZZ
#print axioms edgeCNOT_eq_targetHadamard_CZ
#print axioms edgeOperator_swap

end

end CriticalDepth.Manuscript20261114
