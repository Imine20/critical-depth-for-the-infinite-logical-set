import FaultHistoryGeometry

/-!
The identity circuit used for the universal upper bound. Compress a
minimum-weight physical Pauli, put actual identity gates on its disjoint
midpoint blocks, and apply the reverse adjoint compression.
-/

namespace CriticalDepth.MidpointFaultWitness

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open scoped BigOperators

noncomputable section

variable {n : ℕ}

private theorem reverse_ofFn_prod_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Fin n → Operator ι) (hf : ∀ i j, i ≠ j → Commute (f i) (f j)) :
    (List.ofFn f).reverse.prod = (List.ofFn f).prod := by
  have hp : (List.ofFn f).Pairwise Commute := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact hf _ _ (fun heq => (Nat.ne_of_lt hij) (congrArg Fin.val heq))
  exact (((List.reverse_perm (List.ofFn f)).symm).prod_eq' hp).symm

/-- A layer of supported identity gates has no ideal action. Its listed
gate supports can still host a Pauli fault. -/
def midpointLayer (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q) :
    Layer n (fun _ => 2) q :=
  let S := pauliSupport p
  let e : Fin S.card ≃ S := S.equivFin.symm
  { support := paddedBucket S e q
    gate := fun _ => 1
    disjoint := paddedBucket_disjoint S e q
    arity := paddedBucket_card_le S e q (by omega)
    locality := fun _ => supportedOn_one _
    unitary := fun _ => isUnitary_one }

theorem midpointLayer_eval (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q) :
    (midpointLayer p q hq).eval = 1 := by
  simp [Layer.eval, midpointLayer]

def blockPauli (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q) (i : Fin n) :
    Operator (QubitBasis n) :=
  pauliMatrix 0 (maskPauli p ((midpointLayer p q hq).support i))

theorem blockPauli_supported (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q) (i : Fin n) :
    SupportedOn (blockPauli p q hq i) ((midpointLayer p q hq).support i) :=
  maskPauli_supportedOn _ _

theorem blockPauli_product (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q) :
    (List.ofFn (blockPauli p q hq)).reverse.prod = pauliMatrix 0 p := by
  let L := midpointLayer p q hq
  rw [reverse_ofFn_prod_eq]
  · symm
    apply pauliMatrix_eq_masked_product p L.support L.disjoint
    exact paddedBucket_cover (pauliSupport p) (pauliSupport p).equivFin.symm q hq
  · intro i j hij
    exact (blockPauli_supported p q hq i).commute (blockPauli_supported p q hq j)
      (L.disjoint i j hij)

def midpointCircuit (layers : List (Layer n (fun _ => 2) q))
    (p : Fin n → SinglePauli) (hq : 1 ≤ q) : List (Layer n (fun _ => 2) q) :=
  layers ++ midpointLayer p q hq :: layers.reverse.map Layer.adjoint

theorem midpointCircuit_eval (layers : List (Layer n (fun _ => 2) q))
    (p : Fin n → SinglePauli) (hq : 1 ≤ q) :
    layerSequenceEval (midpointCircuit layers p hq) = 1 := by
  rw [midpointCircuit, layerSequenceEval_append, layerSequenceEval,
    layerSequenceEval_reverse_adjoint, midpointLayer_eval, mul_one]
  exact (layerSequenceEval_isUnitary layers).1

private theorem adjoint_propagate_of_compression
    (U P Q : Operator (QubitBasis n)) (hU : IsUnitary U)
    (h : U * P * U.conjTranspose = Q) :
    propagate U.conjTranspose Q = P := by
  unfold propagate
  rw [← h, Matrix.conjTranspose_conjTranspose]
  have hleft : U.conjTranspose * U = 1 := hU.1
  calc
    _ = (U.conjTranspose * U) * P * (U.conjTranspose * U) := by
      simp only [Matrix.mul_assoc]
    _ = P := by rw [hleft, Matrix.one_mul, Matrix.mul_one]

/-- The circuit has at most the stated depth. Inserting the full disjoint
midpoint block Pauli produces exactly the initial physical Pauli. -/
theorem exists_midpoint_circuit (p : Fin n → SinglePauli) (q h : ℕ)
    (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ (compressingLayers : List (Layer n (fun _ => 2) q)) (p' : Fin n → SinglePauli),
      (midpointCircuit compressingLayers p' (show 1 ≤ q by omega)).length ≤ h ∧
      layerSequenceEval (midpointCircuit compressingLayers p' (show 1 ≤ q by omega)) = 1 ∧
      (pauliSupport p').card = ceilDiv (pauliSupport p).card (q ^ (ceilHalf h - 1)) ∧
      propagate (layerSequenceEval (compressingLayers.reverse.map Layer.adjoint))
        (List.ofFn (blockPauli p' q (show 1 ≤ q by omega))).reverse.prod =
          pauliMatrix 0 p := by
  obtain ⟨compressingLayers, p', hlen, hp, hw⟩ :=
    pauli_compression_sequence q (by omega) p (ceilHalf h - 1)
  refine ⟨compressingLayers, p', ?_, midpointCircuit_eval compressingLayers p' (by omega), ?_, ?_⟩
  · simp only [midpointCircuit, List.length_append, List.length_cons, List.length_map,
      List.length_reverse, hlen]
    unfold ceilHalf
    omega
  · simpa only [compressedWeight_eq_ceilDiv_pow] using hw
  · rw [blockPauli_product, layerSequenceEval_reverse_adjoint]
    exact adjoint_propagate_of_compression _ _ _ (layerSequenceEval_isUnitary compressingLayers) hp

def activeSlots (p : Fin n → SinglePauli) (q : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < ceilDiv (pauliSupport p).card q

theorem activeSlots_card (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q) :
    (activeSlots p q).card = ceilDiv (pauliSupport p).card q := by
  let m := ceilDiv (pauliSupport p).card q
  have hmn : m ≤ n := ceilDiv_support_le_sites _ _ hq
  let e : Fin m ↪ Fin n := ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩
  have he : activeSlots p q = (Finset.univ : Finset (Fin m)).map e := by
    ext i
    simp only [activeSlots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h
      exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨a, rfl⟩
      exact a.isLt
  simp only [he, Finset.card_map, Finset.card_univ, Fintype.card_fin, m]

theorem blockPauli_one_of_not_active (p : Fin n → SinglePauli) (q : ℕ)
    (hq : 1 ≤ q) (i : Fin n) (hi : i ∉ activeSlots p q) :
    blockPauli p q hq i = 1 := by
  have hi' : ¬ i.val < ceilDiv (pauliSupport p).card q :=
    fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
  have hS : (midpointLayer p q hq).support i = ∅ := by
    simp [midpointLayer, paddedBucket, hi']
  change pauliMatrix 0 (maskPauli p ((midpointLayer p q hq).support i)) = 1
  rw [hS, maskPauli_empty, pauliMatrix_zero_eq_tensorEntries]
  exact map_one (tensorEntriesMonoidHom (Fin n))

/-- Faults on either half of the actual nonempty middle gate locations. -/
def partialMidpoint (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q)
    (s : Finset (Fin n)) : Operator (QubitBasis n) :=
  (List.ofFn fun i => if i ∈ s then blockPauli p q hq i else 1).reverse.prod

private theorem partialMidpoint_mul_complement (p : Fin n → SinglePauli) (q : ℕ)
    (hq : 1 ≤ q) (s : Finset (Fin n)) (hs : s ⊆ activeSlots p q) :
    partialMidpoint p q hq s * partialMidpoint p q hq (activeSlots p q \ s) =
      pauliMatrix 0 p := by
  let f i := if i ∈ s then blockPauli p q hq i else 1
  let g i := if i ∈ activeSlots p q \ s then blockPauli p q hq i else 1
  let L := midpointLayer p q hq
  let slots := (List.ofFn (fun i : Fin n => i)).reverse
  have hc (i j : Fin n) : Commute (g i) (f j) := by
    by_cases hi : i ∈ activeSlots p q \ s <;> by_cases hj : j ∈ s
    · have hne : i ≠ j := fun h => (Finset.mem_sdiff.mp hi).2 (h.symm ▸ hj)
      simpa only [g, f, if_pos hi, if_pos hj] using
        (blockPauli_supported p q hq i).commute (blockPauli_supported p q hq j)
          (L.disjoint i j hne)
    · simpa only [f, if_neg hj] using Commute.one_right (g i)
    · simpa only [g, if_neg hi] using Commute.one_left (f j)
    · simpa only [g, if_neg hi] using Commute.one_left (f j)
  have hprod (indices : List (Fin n)) :
      (indices.map f).prod * (indices.map g).prod =
        (indices.map fun i => f i * g i).prod := by
    induction indices with
    | nil => simp
    | cons i tail ih =>
      have hcomm : Commute (g i) (tail.map f).prod := by
        apply Commute.list_prod_right
        intro x h
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
        exact hc i j
      simp only [List.map_cons, List.prod_cons, ← ih]
      calc
        _ = f i * ((tail.map f).prod * g i) * (tail.map g).prod := by simp only [mul_assoc]
        _ = _ := by rw [← hcomm.eq]; simp only [mul_assoc]
  have hsingle (i : Fin n) : f i * g i = blockPauli p q hq i := by
    by_cases hi : i ∈ s
    · simp [f, g, hi]
    · by_cases hit : i ∈ activeSlots p q
      · simp [f, g, hi, hit]
      · simp [f, g, hi, hit, blockPauli_one_of_not_active p q hq i hit]
  have heq := hprod slots
  simp only [slots, List.map_reverse, List.map_ofFn, Function.comp_def, hsingle] at heq
  exact heq.trans (blockPauli_product p q hq)

theorem exists_balanced_midpoint_parts (p : Fin n → SinglePauli) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (s t : Finset (Fin n)),
      Disjoint s t ∧ s ∪ t = activeSlots p q ∧
      max s.card t.card = ceilDiv (ceilDiv (pauliSupport p).card q) 2 ∧
      partialMidpoint p q hq s * partialMidpoint p q hq t = pauliMatrix 0 p := by
  let A := activeSlots p q
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := A) (n := A.card / 2) (by omega)
  refine ⟨s, A \ s, Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi),
    Finset.union_sdiff_of_subset hs, ?_, partialMidpoint_mul_complement p q hq s hs⟩
  rw [Finset.card_sdiff_of_subset hs, hcard, ← activeSlots_card p q hq]
  by_cases h : A.card = 0
  · simp [A, h]
  · rw [ceilDiv_of_pos (Nat.pos_of_ne_zero h)]
    omega

#print axioms exists_balanced_midpoint_parts

#print axioms exists_midpoint_circuit

end
end CriticalDepth.MidpointFaultWitness
