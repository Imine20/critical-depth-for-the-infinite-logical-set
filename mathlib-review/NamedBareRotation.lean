import BarePauliRotations

/-!
# Native logical image from a supplied physical Pauli rotation circuit
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open scoped Kronecker

variable {n K g q h : ℕ}

theorem barePauli_projectiveRotation_of_layer_sequence
    (C : Code n (fun _ => 2) K g) (p : Fin n → SinglePauli)
    (A : Operator (Fin K))
    (hencoded : pauliMatrix 0 p * C.encoding =
      C.encoding * (A ⊗ₖ (1 : Operator (Fin g))))
    (hself : star A = A) (hsq : A*A = 1) (t : ℝ)
    (L : List (Layer n (fun _ => 2) q)) (hL : L.length ≤ h)
    (heval : layerSequenceEval L = rotation (pauliMatrix 0 p) t) :
    projectiveRotation A hself hsq t ∈ nativeLogicalImage C.encoding q h := by
  have hc : circuitEval (circuitOfLayers L) = rotation (pauliMatrix 0 p) t :=
    (circuitOfLayers_eval L).trans heval
  rw [nativeLogicalImage_eq_preimage C.encoding C.isometry]
  change puToProjectiveOperator (Fin K)
      (projectiveMk (Fin K) (unitaryRotation A hself hsq t)) ∈ arbitraryLogicalImageAtMost C q h
  rw [puToProjectiveOperator_mk]
  apply logicalImage_subset_atMost C q L.length h hL
  refine ⟨circuitOfLayers L, rotation A t, ?_, rfl⟩
  rw [hc]
  exact implements_rotation_bare C _ A hencoded hself hsq t

#print axioms barePauli_projectiveRotation_of_layer_sequence

end CriticalDepth.Manuscript20261114
