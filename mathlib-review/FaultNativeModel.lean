import FaultUpperWitness
import FaultLawIndependence
import FaultCPTPOptimality

/-!
Independent Pauli noise on nonempty slots of an exact native circuit.
A layer can carry any native unitary on a slot, including a supported
identity gate. Empty padding slots have no fault locations.
-/

namespace CriticalDepth.FaultNativeModel

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.IndependentFaultHistories
open CriticalDepth.EncodedFaultRecovery CriticalDepth.MidpointFaultWitness
open CriticalDepth.FaultDepthArithmetic
open scoped Kronecker ENat BigOperators

noncomputable section

variable {n q K : ℕ}

abbrev Layers (n q : ℕ) := List (Layer n (fun _ => 2) q)

def supportAt (L : Layers n q) (i : Fin L.length × Fin n) : Finset (Fin n) :=
  (L.get i.1).support i.2

abbrev Location (L : Layers n q) :=
  {i : Fin L.length × Fin n // (supportAt L i).Nonempty}

abbrev FaultLabel {L : Layers n q} (i : Location L) :=
  {p : supportAt L i.val → SinglePauli // p ≠ fun _ => .I}

instance {L : Layers n q} (i : Location L) : Nonempty (FaultLabel i) := by
  obtain ⟨x, hx⟩ := i.property
  refine ⟨⟨fun _ => .X, ?_⟩⟩
  intro h
  have hz := congrFun h ⟨x, hx⟩
  cases hz

/-- Uniform conditional noise is one admissible example. The circuit
bounds quantify over all normalized positive conditional weights. -/
def uniformLaw (L : Layers n q) : Law (fun i : Location L => FaultLabel i) where
  weight i _ := (Fintype.card (FaultLabel i) : ℝ)⁻¹
  positive i _ := inv_pos.mpr (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (FaultLabel i)))
  normalized i := by
    have h : (Fintype.card (FaultLabel i) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (FaultLabel i)).ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ h

def insertion (L : Layers n q) (i : Location L) : Insertion L where
  before := L.take i.val.1.val
  layer := L.get i.val.1
  after := L.drop (i.val.1.val + 1)
  split := by
    have hd := List.drop_eq_getElem_cons i.val.1.isLt
    conv_lhs => rw [← List.take_append_drop i.val.1.val L]
    rw [hd]
    rfl
  slot := i.val.2

def physicalFault {L : Layers n q} (i : Location L) (p : FaultLabel i) :
    Operator (QubitBasis n) :=
  pauliMatrix 0 (extendLocalPauli (supportAt L i.val) p.val)

theorem physicalFault_supported {L : Layers n q} (i : Location L) (p : FaultLabel i) :
    SupportedOn (physicalFault i p) ((insertion L i).layer.support (insertion L i).slot) :=
  pauliMatrix_extendLocalPauli_supportedOn _ _

def fullOrder (L : Layers n q) : List (Location L) :=
  (((List.finRange L.length).flatMap fun j => (List.finRange n).map fun i => (j, i)).filterMap
    fun i => if hi : (supportAt L i).Nonempty then some ⟨i, hi⟩ else none).reverse

theorem mem_fullOrder (L : Layers n q) (i : Location L) : i ∈ fullOrder L := by
  apply List.mem_reverse.mpr
  apply List.mem_filterMap.mpr
  refine ⟨i.val, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    exact ⟨i.val.1, List.mem_finRange _, List.mem_map.mpr ⟨i.val.2, List.mem_finRange _, rfl⟩⟩
  · simp only [dif_pos i.property]

theorem fullOrder_nodup (L : Layers n q) : (fullOrder L).Nodup := by
  apply List.nodup_reverse.mpr
  apply List.Nodup.filterMap
  · intro a b c ha hb
    split at ha
    · split at hb
      · have hac : a = c.val := congrArg Subtype.val (Option.mem_some_iff.mp ha)
        have hbc : b = c.val := congrArg Subtype.val (Option.mem_some_iff.mp hb)
        exact hac.trans hbc.symm
      · simp at hb
    · simp at ha
  · exact (List.nodup_finRange L.length).product (List.nodup_finRange n)

def chronologicalFaults {L : Layers n q} (x : History (fun i : Location L => FaultLabel i)) :
    List (Location L) :=
  (fullOrder L).filter fun i => decide (i ∈ faults x)

theorem mem_chronologicalFaults {L : Layers n q}
    (x : History (fun i : Location L => FaultLabel i)) (i : Location L)
    (hi : i ∈ chronologicalFaults x) : i ∈ faults x := by
  simpa using (List.mem_filter.mp hi).2

def encodedBranch (C : Code n (fun _ => 2) K 1) {L : Layers n q}
    (x : History (fun i : Location L => FaultLabel i)) :
    Matrix (QubitBasis n) (Fin K × Fin 1) ℂ :=
  outputHistory (insertion L) physicalFault x (chronologicalFaults x) * C.encoding

theorem encodedBranch_isometry (C : Code n (fun _ => 2) K 1) {L : Layers n q}
    (x : History (fun i : Location L => FaultLabel i)) :
    (encodedBranch C x).conjTranspose * encodedBranch C x = 1 := by
  have hu := (outputHistory_unitary (insertion L) physicalFault x (chronologicalFaults x)
    (fun _ _ => unphased_pauliMatrix_isUnitary _)).1
  change (outputHistory (insertion L) physicalFault x (chronologicalFaults x)).conjTranspose *
    outputHistory (insertion L) physicalFault x (chronologicalFaults x) = 1 at hu
  simp only [encodedBranch, Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc C.encoding.conjTranspose, hu, Matrix.mul_one, C.isometry]

def circuitInfidelity (C : Code n (fun _ => 2) K 1) (L : Layers n q)
    (μ : Law (fun i : Location L => FaultLabel i)) : ℝ → ℝ :=
  optimalInfidelity μ (encodedBranch C)

theorem native_circuit_exponent_floor [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (d : ℕ) (hdetect : DetectsBelow C d)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i))
    (hq : 1 ≤ q) (W : Operator (Fin K)) (hW : Implements C (layerSequenceEval L) W) :
    (lowerEnvelope q d L.length : ℕ∞) ≤ FaultExponent.exponent (circuitInfidelity C L μ) :=
  circuit_exponent_floor (insertion L) physicalFault physicalFault_supported
    (fun _ _ => unphased_pauliMatrix_isUnitary _) chronologicalFaults mem_chronologicalFaults
    μ hq d C hdetect W hW

/-- An exact implementation at the advertised depth budget together with
its independent positive-weight Pauli law. -/
structure Experiment (C : Code n (fun _ => 2) K 1) (q h : ℕ) where
  layers : Layers n q
  depth : layers.length ≤ h
  logical : Operator (Fin K)
  exactAction : Implements C (layerSequenceEval layers) logical
  law : Law (fun i : Location layers => FaultLabel i)

def perCodeExponent (C : Code n (fun _ => 2) K 1) (q h : ℕ) : ℕ∞ :=
  FaultExponent.worstCaseExponent fun e : Experiment C q h =>
    circuitInfidelity C e.layers e.law

theorem perCodeExponent_floor [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (q d h : ℕ) (hq : 1 ≤ q)
    (hdetect : DetectsBelow C d) :
    (lowerEnvelope q d h : ℕ∞) ≤ perCodeExponent C q h := by
  apply le_iInf
  intro e
  apply le_trans _ (native_circuit_exponent_floor C d hdetect e.layers e.law hq
    e.logical e.exactAction)
  have hden : q ^ e.layers.length + q ≤ q ^ h + q :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) e.depth) _
  have hpos : 0 < q ^ h + q := by omega
  have hpos' : 0 < q ^ e.layers.length + q := by omega
  have hceil := (ceilDiv_le_iff d _ (lowerEnvelope q d e.layers.length) hpos').mp le_rfl
  exact_mod_cast (ceilDiv_le_iff d _ (lowerEnvelope q d e.layers.length) hpos).mpr
    (hceil.trans (Nat.mul_le_mul_left _ hden))

/-- The selected positive conditional weights do not affect the circuit's
optimal entanglement-infidelity exponent. -/
theorem native_circuit_exponent_independent [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (L : Layers n q)
    (μ ν : Law (fun i : Location L => FaultLabel i)) :
    FaultExponent.exponent (circuitInfidelity C L μ) =
      FaultExponent.exponent (circuitInfidelity C L ν) :=
  FaultLawIndependence.encodedExponent_eq_of_positiveLaws μ ν _ (encodedBranch_isometry C)

theorem circuitInfidelity_attained_by_cptp [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (L : Layers n q)
    (μ : Law (fun i : Location L => FaultLabel i)) (p : ℝ) :
    ∃ R : FaultCPTPOptimality.RecoveryChannel (QubitBasis n) (Fin K × Fin 1),
      FaultCPTPOptimality.channelHistoryLoss μ (encodedBranch C) p R = circuitInfidelity C L μ p :=
  FaultCPTPOptimality.exists_cptp_optimalInfidelity μ _ p

#print axioms native_circuit_exponent_independent
#print axioms circuitInfidelity_attained_by_cptp

#print axioms native_circuit_exponent_floor
#print axioms perCodeExponent_floor

end
end CriticalDepth.FaultNativeModel
