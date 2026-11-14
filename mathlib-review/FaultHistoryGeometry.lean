import FaultCircuitSupport
import EncodedFaultRecovery

/-!
Two-frame support for a product of circuit faults. The product is taken
in output order, and the same product is conjugated to the input frame.
-/

namespace CriticalDepth.FaultHistoryGeometry

open CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.FaultDepthArithmetic
open scoped Kronecker BigOperators ENat

noncomputable section

variable {n q K : ℕ} {dim : Fin n → ℕ}

theorem propagate_mul (U A B : PhysicalOperator n dim) (hU : IsUnitary U) :
    propagate U (A * B) = propagate U A * propagate U B := by
  unfold propagate
  have h : U.conjTranspose * U = 1 := hU.1
  calc
    U * (A * B) * U.conjTranspose =
        U * (A * ((U.conjTranspose * U) * B)) * U.conjTranspose := by rw [h, one_mul]
    _ = (U * A * U.conjTranspose) * (U * B * U.conjTranspose) := by
      simp only [Matrix.mul_assoc]

private theorem propagate_adjoint (U A : PhysicalOperator n dim) :
    propagate U A.conjTranspose = (propagate U A).conjTranspose := by
  simp only [propagate, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private theorem propagate_isUnitary (U A : PhysicalOperator n dim)
    (hU : IsUnitary U) (hA : IsUnitary A) : IsUnitary (propagate U A) :=
  isUnitary_mul (isUnitary_mul hU hA) (isUnitary_star hU)

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

/-- One location is represented by its actual layer and gate slot,
with an exact split of the ideal circuit on both sides of that layer. -/
structure Insertion (layers : List (Layer n dim q)) where
  before : List (Layer n dim q)
  layer : Layer n dim q
  after : List (Layer n dim q)
  split : layers = before ++ layer :: after
  slot : Fin n

variable {layers : List (Layer n dim q)}

def Insertion.layerNumber (loc : Insertion layers) : ℕ := loc.before.length + 1

def Insertion.outputSupport (loc : Insertion layers) : Finset (Fin n) :=
  layerSequenceCone loc.after (loc.layer.support loc.slot)

def Insertion.inputSupport (loc : Insertion layers) : Finset (Fin n) :=
  layerSequenceCone (loc.before.reverse.map Layer.adjoint) (loc.layer.support loc.slot)

def outputFault (loc : Loc → Insertion layers)
    (P : ∀ i, Label i → PhysicalOperator n dim) (x : History Label) (i : Loc) :
    PhysicalOperator n dim :=
  (x i).elim 1 (fun a => propagate (layerSequenceEval (loc i).after) (P i a))

/-- The listed faulty locations are supplied in the circuit's reverse
execution order. Clean slots contribute the identity and may be omitted. -/
def outputHistory (loc : Loc → Insertion layers)
    (P : ∀ i, Label i → PhysicalOperator n dim) (x : History Label)
    (order : List Loc) : PhysicalOperator n dim :=
  (order.map (outputFault loc P x)).prod

theorem outputHistory_unitary (loc : Loc → Insertion layers)
    (P : ∀ i, Label i → PhysicalOperator n dim) (x : History Label)
    (order : List Loc) (hP : ∀ i a, IsUnitary (P i a)) :
    IsUnitary (outputHistory loc P x order) := by
  apply matrixList_prod_isUnitary
  intro A hA
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hA
  cases ha : x i with
  | none => simpa [outputFault, ha] using (isUnitary_one (ι := PhysicalBasis n dim))
  | some a =>
    simpa only [outputFault, ha, Option.elim_some] using
      propagate_isUnitary _ _ (layerSequenceEval_isUnitary (loc i).after) (hP i a)

private theorem outputFault_support (loc : Loc → Insertion layers)
    (P : ∀ i, Label i → PhysicalOperator n dim)
    (hP : ∀ i a, SupportedOn (P i a) ((loc i).layer.support (loc i).slot))
    (x : History Label) (i : Loc) (hiq : 1 ≤ q) :
    SupportedOn (outputFault loc P x i) (loc i).outputSupport := by
  cases ha : x i with
  | none => simpa [outputFault, ha] using supportedOn_one (loc i).outputSupport
  | some a =>
    simpa only [outputFault, ha, Option.elim_some, Insertion.outputSupport] using
      (outputInsertionCone (loc i).layer (loc i).after (loc i).slot _ (hP i a) hiq).1

private theorem inputFault_support (loc : Loc → Insertion layers)
    (P : ∀ i, Label i → PhysicalOperator n dim)
    (hP : ∀ i a, SupportedOn (P i a) ((loc i).layer.support (loc i).slot))
    (x : History Label) (i : Loc) (hiq : 1 ≤ q) :
    SupportedOn (propagate (layerSequenceEval layers).conjTranspose (outputFault loc P x i))
      (loc i).inputSupport := by
  cases ha : x i with
  | none =>
    have hU := (layerSequenceEval_isUnitary layers).1
    change (layerSequenceEval layers).conjTranspose * layerSequenceEval layers = 1 at hU
    simpa [outputFault, ha, propagate, hU] using supportedOn_one (loc i).inputSupport
  | some a =>
    simp only [outputFault, ha, Option.elim_some]
    rw [show layerSequenceEval layers =
      layerSequenceEval ((loc i).before ++ (loc i).layer :: (loc i).after) from
        congrArg layerSequenceEval (loc i).split, pullbackOutputInsertion]
    exact (inputInsertionCone (loc i).before (loc i).layer (loc i).slot _ (hP i a) hiq).1

private theorem subspace_scalarCompression (C : Code n dim K 1)
    (T : PhysicalOperator n dim) (hT : GaugeOnly C T) :
    ∃ a : ℂ, C.encoding.conjTranspose * T * C.encoding =
      a • (1 : Operator (Fin K × Fin 1)) := by
  obtain ⟨M, hM⟩ := hT
  refine ⟨M 0 0, hM.trans ?_⟩
  ext ⟨i, a⟩ ⟨j, b⟩
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a
  subst b
  simp [Matrix.kronecker_apply, Matrix.one_apply, Matrix.smul_apply, mul_comm]

theorem histories_scalarCrossTerm (loc : Loc → Insertion layers)
    (P : ∀ i, Label i → PhysicalOperator n dim)
    (hP : ∀ i a, SupportedOn (P i a) ((loc i).layer.support (loc i).slot))
    (x y : History Label) (order : History Label → List Loc)
    (horder : ∀ z i, i ∈ order z → i ∈ faults z)
    (hq : 1 ≤ q) (d r : ℕ)
    (hx : (faults x).card ≤ r) (hy : (faults y).card ≤ r)
    (hr : r < lowerEnvelope q d layers.length)
    (C : Code n dim K 1) (hdet : DetectsBelow C d)
    (W : Operator (Fin K)) (Z : Operator (Fin 1))
    (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hV : layerSequenceEval layers * C.encoding = C.encoding * (W ⊗ₖ Z))
    (hdual : C.encoding.conjTranspose * layerSequenceEval layers =
      (W ⊗ₖ Z) * C.encoding.conjTranspose) :
    ∃ a : ℂ,
      (outputHistory loc P x (order x) * C.encoding).conjTranspose *
        (outputHistory loc P y (order y) * C.encoding) =
          a • (1 : Operator (Fin K × Fin 1)) := by
  classical
  let U := layerSequenceEval layers
  let X := outputHistory loc P x (order x)
  let Y := outputHistory loc P y (order y)
  let sites := (faults x).disjSum (faults y)
  let j : Loc ⊕ Loc → ℕ := Sum.elim (fun i => (loc i).layerNumber) (fun i => (loc i).layerNumber)
  let S : Loc ⊕ Loc → Finset (Fin n) :=
    Sum.elim (fun i => (loc i).inputSupport) (fun i => (loc i).inputSupport)
  let T : Loc ⊕ Loc → Finset (Fin n) :=
    Sum.elim (fun i => (loc i).outputSupport) (fun i => (loc i).outputSupport)
  have unionSupport (B : Loc → Finset (Fin n)) :
      (faults x).biUnion B ∪ (faults y).biUnion B ⊆
        sites.biUnion (Sum.elim B B) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_biUnion.mpr ⟨.inl i, Finset.inl_mem_disjSum.mpr hi, hai⟩
    · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_biUnion.mpr ⟨.inr i, Finset.inr_mem_disjSum.mpr hi, hai⟩
  have houtput (z : History Label) :
      SupportedOn (outputHistory loc P z (order z)) ((faults z).biUnion fun i => (loc i).outputSupport) :=
    productSupported (faults z) (order z) _ (outputFault loc P z) (horder z)
      (fun i _ => outputFault_support loc P hP z i hq)
  have hinput (z : History Label) :
      SupportedOn (propagate U.conjTranspose (outputHistory loc P z (order z)))
        ((faults z).biUnion fun i => (loc i).inputSupport) := by
    unfold outputHistory
    rw [pullbackFaultProduct U (layerSequenceEval_isUnitary layers), List.map_map]
    exact productSupported (faults z) (order z) _ _ (horder z)
      (fun i _ => inputFault_support loc P hP z i hq)
  have hU : IsUnitary U := layerSequenceEval_isUnitary layers
  have hout : SupportedOn (X.conjTranspose * Y) (sites.biUnion T) :=
    ((houtput x).conjTranspose.mul (houtput y)).mono (unionSupport _)
  have hin : SupportedOn (propagate U.conjTranspose (X.conjTranspose * Y)) (sites.biUnion S) := by
    have huAdj : IsUnitary U.conjTranspose := isUnitary_star hU
    rw [propagate_mul _ _ _ huAdj, propagate_adjoint]
    exact ((hinput x).conjTranspose.mul (hinput y)).mono (unionSupport _)
  have hcard : sites.card ≤ 2 * r := by
    rw [Finset.card_disjSum, two_mul]
    exact Nat.add_le_add hx hy
  have hnum (i : Loc) : 1 ≤ (loc i).layerNumber ∧ (loc i).layerNumber ≤ layers.length := by
    have heq := congrArg List.length (loc i).split
    simp only [List.length_append, List.length_cons] at heq
    unfold Insertion.layerNumber
    omega
  have hsizeIn (i : Loc) : (loc i).inputSupport.card ≤ q ^ (loc i).layerNumber :=
    (inputInsertionCone (loc i).before (loc i).layer (loc i).slot 1
      (supportedOn_one _) hq).2
  have hsizeOut (i : Loc) :
      (loc i).outputSupport.card ≤ q ^ (layers.length - (loc i).layerNumber + 1) := by
    have heq := congrArg List.length (loc i).split
    simp only [List.length_append, List.length_cons] at heq
    rw [show layers.length - (loc i).layerNumber = (loc i).after.length by
      unfold Insertion.layerNumber
      omega]
    exact (outputInsertionCone (loc i).layer (loc i).after (loc i).slot 1
      (supportedOn_one _) hq).2
  have hgauge :=
    pairedCrossTerm_detected sites q d layers.length r j S T
      (propagate U.conjTranspose (X.conjTranspose * Y)) (X.conjTranspose * Y) U C
      hq hcard hr (by rintro (i|i) _ <;> exact hnum i)
      (by rintro (i|i) _ <;> exact hsizeIn i)
      (by rintro (i|i) _ <;> exact hsizeOut i) hin hout rfl hdet hU W Z hW hZ hV hdual
  obtain ⟨a, ha⟩ := subspace_scalarCompression C _ hgauge
  exact ⟨a, by simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc, X, Y] using ha⟩

/-- The floor applies to propagated histories of native gates on the actual
encoded subspace. Its recovery acts on the register only at the end. -/
theorem circuit_exponent_floor [Nonempty (Fin K × Fin 1)]
    (loc : Loc → Insertion layers) (P : ∀ i, Label i → PhysicalOperator n dim)
    (hP : ∀ i a, SupportedOn (P i a) ((loc i).layer.support (loc i).slot))
    (huP : ∀ i a, IsUnitary (P i a))
    (order : History Label → List Loc) (horder : ∀ z i, i ∈ order z → i ∈ faults z)
    (μ : Law Label) (hq : 1 ≤ q) (d : ℕ) (C : Code n dim K 1)
    (hdet : DetectsBelow C d) (W : Operator (Fin K))
    (himpl : Implements C (layerSequenceEval layers) W) :
    (lowerEnvelope q d layers.length : ℕ∞) ≤ FaultExponent.exponent
      (optimalInfidelity μ fun x => outputHistory loc P x (order x) * C.encoding) := by
  obtain ⟨hW, Z, hZ, hV⟩ := himpl
  have hdual : C.encoding.conjTranspose * layerSequenceEval layers =
      (W ⊗ₖ Z) * C.encoding.conjTranspose := by
    have heval := circuitOfLayers_eval layers
    rw [← heval] at hV ⊢
    exact point_encoded_dual C (circuitOfLayers layers) W Z hW hZ hV
  apply guaranteed_exponent_of_scalarCrossTerms μ
  · intro x
    have hunit := (outputHistory_unitary loc P x (order x) huP).1
    change (outputHistory loc P x (order x)).conjTranspose *
      outputHistory loc P x (order x) = 1 at hunit
    simp only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc C.encoding.conjTranspose, hunit, Matrix.mul_one, C.isometry]
  · intro x y hx hy
    exact histories_scalarCrossTerm loc P hP x y order horder hq d
      (max (faults x).card (faults y).card) (le_max_left _ _) (le_max_right _ _)
      (max_lt hx hy) C hdet W Z hW hZ hV hdual

#print axioms circuit_exponent_floor
#print axioms histories_scalarCrossTerm

end
end CriticalDepth.FaultHistoryGeometry
