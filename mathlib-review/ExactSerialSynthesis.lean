import CriticalDepthMathlib
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Serial physical depth for a finite exact logical word
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped BigOperators Kronecker

noncomputable section

variable {n K g q : ℕ} {dim : Fin n → ℕ}

private theorem list_nativeLayer_eval_append (L R : List (NativeLayer n dim)) :
    ((L ++ R).map nativeLayerEval).reverse.prod =
      (R.map nativeLayerEval).reverse.prod * (L.map nativeLayerEval).reverse.prod := by
  simp only [List.map_append, List.reverse_append, List.prod_append]

private theorem nativeList_circuit_eval (L : List (NativeLayer n dim)) :
    nativeCircuitEval (fun i : Fin L.length => L[i]) = (L.map nativeLayerEval).reverse.prod := by
  unfold nativeCircuitEval
  change (List.ofFn (fun i : Fin L.length => nativeLayerEval (L[i]))).reverse.prod = _
  exact congrArg (fun l : List (Matrix.unitaryGroup (PhysicalBasis n dim) ℂ) => l.reverse.prod)
    (List.ofFn_getElem_eq_map L nativeLayerEval)

private theorem nativeCircuit_list_eval {r : ℕ} (c : NativeCircuit n dim r) :
    ((List.ofFn c).map nativeLayerEval).reverse.prod = nativeCircuitEval c := by
  unfold nativeCircuitEval
  rw [List.map_ofFn]
  rfl

/-- Execute two words in order, keeping the gauges and exact encoding
factorization. -/
theorem nativeLogicalImage_mul {V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ}
    {a b : PU (Fin K)} {d e : ℕ}
    (ha : a ∈ nativeLogicalImage V q d) (hb : b ∈ nativeLogicalImage V q e) :
    a * b ∈ nativeLogicalImage V q (d + e) := by
  obtain ⟨r, hr, c, hc, W, Z, hC, rfl⟩ := ha
  obtain ⟨s, hs, u, hu, A, B, hU, rfl⟩ := hb
  let L := List.ofFn u ++ List.ofFn c
  let f : NativeCircuit n dim L.length := fun i => L[i]
  have hAllowed : NativeCircuitAllowed q f := by
    intro i
    have hi : f i ∈ L := List.getElem_mem _
    rcases List.mem_append.mp hi with h | h
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
      rw [← hj]
      exact hu j
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
      rw [← hj]
      exact hc j
  refine ⟨L.length, ?_, f, hAllowed, W * A, Z * B, ?_, map_mul _ _ _⟩
  · simp only [L, List.length_append, List.length_ofFn]
    omega
  · change (nativeCircuitEval (fun i : Fin L.length => L[i])).val * V = _
    rw [nativeList_circuit_eval, list_nativeLayer_eval_append, nativeCircuit_list_eval,
      nativeCircuit_list_eval]
    change ((nativeCircuitEval c).val * (nativeCircuitEval u).val) * V =
      V * ((W.val * A.val) ⊗ₖ (Z.val * B.val))
    rw [Matrix.mul_assoc, hU, ← Matrix.mul_assoc, hC, Matrix.mul_assoc,
      ← Matrix.mul_kronecker_mul]

/-- A word of r primitives, each physically implementable at depth d,
has a complete exact realization at depth at most r d. -/
theorem nativeLogicalImage_list_prod
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) (q d : ℕ)
    (L : List (PU (Fin K))) (h : ∀ U ∈ L, U ∈ nativeLogicalImage V q d) :
    L.prod ∈ nativeLogicalImage V q (L.length * d) := by
  induction L with
  | nil =>
    let c : NativeCircuit n dim 0 := fun i => Fin.elim0 i
    have hc : NativeCircuitAllowed q c := fun i => Fin.elim0 i
    refine ⟨0, Nat.zero_le _, c, hc, 1, 1, ?_, map_one _⟩
    change (nativeCircuitEval c).val * V = V * ((1 : Operator (Fin K)) ⊗ₖ (1 : Operator (Fin g)))
    simp [nativeCircuitEval, c, Matrix.one_kronecker_one]
  | cons a L ih =>
    simp only [List.prod_cons, List.length_cons]
    rw [Nat.succ_mul, Nat.add_comm (L.length * d)]
    exact nativeLogicalImage_mul (h a (List.mem_cons_self ..))
      (ih (fun U hU => h U (List.mem_cons_of_mem a hU)))

#print axioms nativeLogicalImage_mul
#print axioms nativeLogicalImage_list_prod

end

end CriticalDepth.Manuscript20261114
