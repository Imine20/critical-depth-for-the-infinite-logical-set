import MidpointFaultWitness
import FaultStabilizerTrace

/-!
The two balanced sets of faulted native midpoint gates give encoded
isometries that differ by a traceless logical Pauli.
-/

namespace CriticalDepth.FaultUpperWitness

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.MidpointFaultWitness CriticalDepth.FaultDepthArithmetic
open scoped Kronecker

noncomputable section

variable {n : ℕ}

private theorem partialMidpoint_unitary (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q)
    (s : Finset (Fin n)) : IsUnitary (partialMidpoint p q hq s) := by
  classical
  apply matrixList_prod_isUnitary
  intro A hA
  simp only [List.mem_reverse, List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  split_ifs
  · exact unphased_pauliMatrix_isUnitary _
  · exact isUnitary_one

private theorem partialMidpoint_selfAdjoint (p : Fin n → SinglePauli) (q : ℕ)
    (hq : 1 ≤ q) (s : Finset (Fin n)) :
    (partialMidpoint p q hq s).conjTranspose = partialMidpoint p q hq s := by
  classical
  let F : Fin n → Operator (QubitBasis n) :=
    fun i => if i ∈ s then blockPauli p q hq i else 1
  let L := midpointLayer p q hq
  have hF (i : Fin n) : star (F i) = F i := by
    by_cases hi : i ∈ s
    · have h : star (blockPauli p q hq i) = blockPauli p q hq i :=
        unphased_pauliMatrix_selfAdjoint (maskPauli p (L.support i))
      simpa only [F, if_pos hi] using h
    · simp [F, hi]
  have hcomm (i j : Fin n) (hij : i ≠ j) : Commute (F i) (F j) := by
    have hsupp (i : Fin n) : SupportedOn (F i) (L.support i) := by
      by_cases hi : i ∈ s
      · simp only [F, hi, if_true]
        exact blockPauli_supported _ _ _ _
      · simp only [F, hi, if_false]
        exact supportedOn_one _
    exact (hsupp i).commute (hsupp j) (L.disjoint _ _ hij)
  change star (List.ofFn F).reverse.prod = (List.ofFn F).reverse.prod
  rw [star_matrixList_prod]
  simp only [List.reverse_reverse, List.map_ofFn]
  have heq : star ∘ F = F := funext hF
  rw [heq]
  have hp : (List.ofFn F).Pairwise Commute := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact hcomm _ _ (fun heq => (Nat.ne_of_lt hij) (congrArg Fin.val heq))
  exact (((List.reverse_perm (List.ofFn F)).symm).prod_eq' hp)

private theorem pow_pred_mul (q h : ℕ) (hh : 1 ≤ h) :
    q ^ (ceilHalf h - 1) * q = q ^ ceilHalf h := by
  rw [← pow_succ]
  congr 1
  unfold ceilHalf
  omega

/-- At most the upper-envelope count of native midpoint faults per history
is sufficient for two indistinguishable logical branches at depth at most h. -/
theorem exists_midpoint_ambiguous_branches {k d : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstabilizer : IsStabilizer C)
    (hdistance : HasActualDistance C d) (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ (layers : List (Layer n (fun _ => 2) q)) (p' : Fin n → SinglePauli)
      (s t : Finset (Fin n)) (W : Operator (Fin (2 ^ k))),
      (midpointCircuit layers p' (show 1 ≤ q by omega)).length ≤ h ∧
      layerSequenceEval (midpointCircuit layers p' (show 1 ≤ q by omega)) = 1 ∧
      max s.card t.card = upperEnvelope q d h ∧
      Disjoint s t ∧ s ∪ t = activeSlots p' q ∧ W.trace = 0 ∧
      IsUnitary W ∧
      propagate (layerSequenceEval (layers.reverse.map Layer.adjoint))
        (partialMidpoint p' q (show 1 ≤ q by omega) t) * C.encoding =
      (propagate (layerSequenceEval (layers.reverse.map Layer.adjoint))
        (partialMidpoint p' q (show 1 ≤ q by omega) s) * C.encoding) *
          (W ⊗ₖ (1 : Operator (Fin 1))) := by
  obtain ⟨p, W, hw, hENC, hWA, hW₂, hWt⟩ :=
    FaultStabilizerTrace.stabilizer_exact_traceless_logicalPauli C hstabilizer hdistance
  have hq' : 1 ≤ q := by omega
  obtain ⟨layers, p', hlength, heval, hweight, hfull⟩ := exists_midpoint_circuit p q h hq hh
  obtain ⟨s, t, hdisj, hc, hcount, hpart⟩ := exists_balanced_midpoint_parts p' q hq'
  have hcnt : max s.card t.card = upperEnvelope q d h := by
    rw [hcount, hweight, ceilDiv_comp _ _ q, pow_pred_mul q h hh, hw, midpointHistoryCount]
  have hW : IsUnitary W := by constructor <;> rw [hWA, hW₂]
  refine ⟨layers, p', s, t, W, hlength, heval, hcnt, hdisj, hc, hWt, hW, ?_⟩
  let U := layerSequenceEval (layers.reverse.map Layer.adjoint)
  let A := partialMidpoint p' q hq' s
  let B := partialMidpoint p' q hq' t
  have hU : IsUnitary U := layerSequenceEval_isUnitary _
  have hA : A * A = 1 := by
    have h := (partialMidpoint_unitary p' q hq' s).1
    change A.conjTranspose * A = 1 at h
    rwa [partialMidpoint_selfAdjoint p' q hq' s] at h
  have hphys : propagate U A * propagate U B = pauliMatrix 0 p := by
    rw [← FaultHistoryGeometry.propagate_mul U A B hU]
    change propagate U (partialMidpoint p' q hq' s * partialMidpoint p' q hq' t) = _
    rw [hpart, ← blockPauli_product p' q hq']
    exact hfull
  have hinv : propagate U A * propagate U A = 1 := by
    rw [← FaultHistoryGeometry.propagate_mul U A A hU, hA]
    unfold propagate
    rw [Matrix.mul_one]
    exact hU.2
  change propagate U B * C.encoding = (propagate U A * C.encoding) * _
  calc
    _ = propagate U A * (propagate U A * propagate U B) * C.encoding := by
      rw [← mul_assoc, hinv, one_mul]
    _ = _ := by
      rw [hphys, Matrix.mul_assoc, hENC, ← Matrix.mul_assoc]

#print axioms exists_midpoint_ambiguous_branches

end
end CriticalDepth.FaultUpperWitness
