import FaultUpperWitness
import FaultNativeModel

/-!
The midpoint can apply the prescribed minimum-weight logical Pauli,
using the same supported disjoint fault locations.
-/

namespace CriticalDepth.MidpointFaultWitness

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultNativeModel
open CriticalDepth.FaultDepthArithmetic
open scoped Kronecker BigOperators

noncomputable section
variable {n q : ℕ}

def midpointPauliLayer (p : Fin n → SinglePauli) (hq : 1 ≤ q) :
    Layer n (fun _ => 2) q :=
  { midpointLayer p q hq with
    gate := blockPauli p q hq
    locality := blockPauli_supported p q hq
    unitary := fun _ => unphased_pauliMatrix_isUnitary _ }

def midpointPauliCircuit (A : Layers n q) (p : Fin n → SinglePauli) (hq : 1 ≤ q) : Layers n q :=
  A ++ midpointPauliLayer p hq :: A.reverse.map Layer.adjoint

theorem midpointPauliCircuit_eq_length (A : Layers n q) (p : Fin n → SinglePauli) (hq : 1 ≤ q) :
    (midpointPauliCircuit A p hq).length = (midpointCircuit A p hq).length := by
  simp only [midpointPauliCircuit, midpointCircuit, List.length_append, List.length_cons]

theorem midpointPauliCircuit_eval (A : Layers n q) (p : Fin n → SinglePauli) (hq : 1 ≤ q) :
    layerSequenceEval (midpointPauliCircuit A p hq) =
      propagate (layerSequenceEval (A.reverse.map Layer.adjoint)) (pauliMatrix 0 p) := by
  unfold midpointPauliCircuit
  rw [layerSequenceEval_append, layerSequenceEval]
  change layerSequenceEval (A.reverse.map Layer.adjoint) * (List.ofFn (blockPauli p q hq)).reverse.prod *
    layerSequenceEval A = _
  rw [blockPauli_product]
  unfold propagate
  rw [layerSequenceEval_reverse_adjoint, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

theorem exists_midpointPauliCircuit_of_support_word
    (p : Fin n → SinglePauli) (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ (A : Layers n q) (p' : Fin n → SinglePauli),
      (midpointPauliCircuit A p' (by omega)).length ≤ h ∧
      layerSequenceEval (midpointPauliCircuit A p' (by omega)) = pauliMatrix 0 p ∧
      (activeSlots p' q).card = ceilDiv (pauliSupport p).card (q ^ ceilHalf h) := by
  obtain ⟨A, p', hL, _, hw, hp⟩ := exists_midpoint_circuit p q h hq hh
  refine ⟨A, p', (midpointPauliCircuit_eq_length A p' _).trans_le hL, ?_, ?_⟩
  · rw [midpointPauliCircuit_eval]
    simpa only [blockPauli_product] using hp
  · rw [activeSlots_card p' q (by omega), hw, ceilDiv_comp, ← pow_succ]
    rw [show ceilHalf h - 1 + 1 = ceilHalf h by unfold ceilHalf; omega]

theorem exists_midpointPauli_logical
    {k d : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hS : IsStabilizer C) (hd : HasActualDistance C d) (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ (A : Layers n q) (p' : Fin n → SinglePauli) (W : Operator (Fin (2 ^ k))),
      (midpointPauliCircuit A p' (by omega)).length ≤ h ∧
      Implements C (layerSequenceEval (midpointPauliCircuit A p' (by omega))) W ∧
      W.trace = 0 ∧ (activeSlots p' q).card = ceilDiv d (q ^ ceilHalf h) := by
  obtain ⟨p, W, hw, hENC, hAdj, hSq, hTrace⟩ :=
    FaultStabilizerTrace.stabilizer_exact_traceless_logicalPauli C hS hd
  obtain ⟨A, p', hLen, hEval, hBlocks⟩ := exists_midpointPauliCircuit_of_support_word p q h hq hh
  have hW : IsUnitary W := by constructor <;> rw [hAdj, hSq]
  refine ⟨A, p', W, hLen, ⟨hW, 1, isUnitary_one, ?_⟩, hTrace, ?_⟩
  · rw [hEval]
    exact hENC
  · rwa [hw] at hBlocks

#print axioms exists_midpointPauli_logical

end
end CriticalDepth.MidpointFaultWitness
