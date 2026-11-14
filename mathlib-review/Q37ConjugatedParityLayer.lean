import Q37NativeParityLayer
import FaultOnSiteSupport

/-!
# Changing the local basis of a native parity-phase layer
-/

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.FaultSupportPreserving
open CriticalDepth.FaultCircuitSupport Matrix

variable {n q : ℕ}

private theorem conj_isUnitary (V O : Operator (QubitBasis n))
    (hV : IsUnitary V) (hO : IsUnitary O) :
    IsUnitary (V * O * V.conjTranspose) := by
  have hV' : IsUnitary V.conjTranspose := by
    constructor
    · change V.conjTranspose.conjTranspose * V.conjTranspose = 1
      rw [Matrix.conjTranspose_conjTranspose]
      exact hV.2
    · change V.conjTranspose * V.conjTranspose.conjTranspose = 1
      rw [Matrix.conjTranspose_conjTranspose]
      exact hV.1
  exact isUnitary_mul (isUnitary_mul hV hO) hV'

/-- Conjugation by the same on-site tensor unitary changes the matrix
of the gate while retaining its support and arity. -/
noncomputable def conjugateNativeGate (v : Fin n → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) (G : ListGate n (fun _ => 2) q) :
    ListGate n (fun _ => 2) q where
  support := G.support
  gate := tensorEntries v * G.gate * (tensorEntries v).conjTranspose
  arity := G.arity
  locality := preservesSupports_tensorEntries v hv G.gate G.support G.locality
  unitary := conj_isUnitary _ _ (isUnitary_tensorEntries v hv) G.unitary

/-- All gates in a layer can be conjugated simultaneously by the same
on-site basis change, with the original physical supports. -/
noncomputable def conjugateNativeLayer (v : Fin n → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) (L : ArbitraryLayer n (fun _ => 2) q) :
    ArbitraryLayer n (fun _ => 2) q where
  gates := L.gates.map (conjugateNativeGate v hv)
  disjoint := by rw [List.pairwise_map]; exact L.disjoint

private theorem listGateEval_conjugate (v : Fin n → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) (gates : List (ListGate n (fun _ => 2) q)) :
    listGateEval (gates.map (conjugateNativeGate v hv)) =
      tensorEntries v * listGateEval gates * (tensorEntries v).conjTranspose := by
  let V : Operator (QubitBasis n) := tensorEntries v
  have hV := isUnitary_tensorEntries v hv
  have hLeft : V.conjTranspose * V = 1 := hV.1
  have hRight : V * V.conjTranspose = 1 := hV.2
  induction gates with
  | nil =>
    change (1 : Operator (QubitBasis n)) = V * 1 * V.conjTranspose
    rw [Matrix.mul_one, hRight]
  | cons G tail ih =>
    rw [List.map_cons, listGateEval_cons, listGateEval_cons, ih]
    change (V * listGateEval tail * V.conjTranspose) * (V * G.gate * V.conjTranspose) =
      V * (listGateEval tail * G.gate) * V.conjTranspose
    calc
      _ = V * listGateEval tail * (V.conjTranspose * V) * G.gate * V.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLeft, Matrix.mul_one, Matrix.mul_assoc V (listGateEval tail)]

theorem conjugateNativeLayer_eval (v : Fin n → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) (L : ArbitraryLayer n (fun _ => 2) q) :
    (conjugateNativeLayer v hv L).eval =
      tensorEntries v * L.eval * (tensorEntries v).conjTranspose :=
  listGateEval_conjugate v hv L.gates

private theorem conjugate_filterNonempty (v : Fin n → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) (gates : List (ListGate n (fun _ => 2) q)) :
    filterNonemptyGates (gates.map (conjugateNativeGate v hv)) =
      (filterNonemptyGates gates).map (conjugateNativeGate v hv) := by
  induction gates with
  | nil => rfl
  | cons G tail ih =>
    by_cases hG : G.support = ∅
    · simp only [List.map_cons, filterNonemptyGates, conjugateNativeGate, ite_eq_left hG, ih]
    · simp only [List.map_cons, filterNonemptyGates, conjugateNativeGate, ite_eq_right hG, ih]

/-- The same basis change commutes with padded-layer normalization at
the level of the evaluated matrix. -/
theorem conjugateNativeLayer_normalized_eval (v : Fin n → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) (L : ArbitraryLayer n (fun _ => 2) q) :
    (conjugateNativeLayer v hv L).normalized.eval =
      tensorEntries v * L.normalized.eval * (tensorEntries v).conjTranspose := by
  rw [ArbitraryLayer.normalized_eval, ArbitraryLayer.normalized_eval]
  change listGateEval (filterNonemptyGates (L.gates.map (conjugateNativeGate v hv))) = _
  rw [conjugate_filterNonempty]
  exact listGateEval_conjugate v hv _

/-- The parity layer remains one native layer when its gates are written
in any tensor-product basis, in particular the Hadamard basis. -/
theorem conjugateParityPhaseLayer_normalized_eval (z : Circle)
    (blocks : List {S : Finset (Fin n) // S.card ≤ q})
    (hdis : blocks.Pairwise fun A B => Disjoint A.val B.val)
    (hne : ∀ S ∈ blocks, S.val.Nonempty)
    (v : Fin n → Operator (Fin 2)) (hv : ∀ i, IsUnitary (v i)) :
    (conjugateNativeLayer v hv (parityPhaseLayer z blocks hdis)).normalized.eval =
      tensorEntries v * Matrix.diagonal (fun x => (z : ℂ) ^ countOddBlocks blocks x) *
        (tensorEntries v).conjTranspose := by
  rw [conjugateNativeLayer_normalized_eval, parityPhaseLayer_normalized_eval z blocks hdis hne]

#print axioms conjugateNativeLayer_normalized_eval
#print axioms conjugateParityPhaseLayer_normalized_eval

end CriticalDepth.Q37BinaryData
