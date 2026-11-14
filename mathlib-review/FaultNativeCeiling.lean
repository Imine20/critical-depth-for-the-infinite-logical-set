import FaultNativeModel

/-! The midpoint branches are actual histories of the independent native
gate model, with all other gate locations clean. -/

namespace CriticalDepth.FaultNativeCeiling

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultNativeModel CriticalDepth.FaultHistoryGeometry
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.MidpointFaultWitness CriticalDepth.FaultDepthArithmetic
open scoped Kronecker ENat BigOperators

noncomputable section

variable {n q : ℕ}

private theorem list_prod_filter_ite {ι M : Type*} [Monoid M]
    (T : ι → Prop) [DecidablePred T] (f : ι → M) (l : List ι) :
    ((l.filter fun i => decide (T i)).map f).prod =
      (l.map fun i => if T i then f i else 1).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : T i <;> simp [hi, ih]

variable (A : Layers n q) (p : Fin n → SinglePauli) (hq : 1 ≤ q)

local notation "L" => midpointCircuit A p hq
local notation "M" => midpointLayer p q hq

private def middle : Fin (L).length :=
  ⟨A.length, by simp [midpointCircuit]⟩

private theorem midpoint_get :
    (L).get (middle A p hq) = M := by
  change (A ++ M :: A.reverse.map Layer.adjoint)[A.length] = _
  simp

private theorem midpoint_after :
    (L).drop ((middle A p hq).val + 1) = A.reverse.map Layer.adjoint := by
  simp [midpointCircuit, middle, List.drop_append]

private theorem active_contains_nonidentity (i : Fin n) (hi : i ∈ activeSlots p q) :
    ∃ j : Fin n, j ∈ (M).support i ∧ p j ≠ .I := by
  have hm := (Finset.mem_filter.mp hi).2
  let S := pauliSupport p
  let e : Fin S.card ≃ S := S.equivFin.symm
  let k : Fin (ceilDiv S.card q) := ⟨i.val, hm⟩
  have hqpos : 0 < q := by omega
  let j := bucketPivot S e q hqpos k
  have hj := bucketPivot_mem S e q hqpos k
  have hjS := rankBucket_subset S e q k.val hj
  refine ⟨j, ?_, (Finset.mem_filter.mp hjS).2⟩
  simpa only [midpointLayer, paddedBucket, hm, if_true, S, e, k] using hj

private def middleLocation (i : Fin n) (hi : i ∈ activeSlots p q) : Location L :=
  ⟨(middle A p hq, i), by
    obtain ⟨j, hj, _⟩ := active_contains_nonidentity p hq i hi
    exact ⟨j, by simpa only [supportAt, midpoint_get A p hq] using hj⟩⟩

private def subsetHistory (s : Finset (Fin n)) :
    History (fun i : Location L => FaultLabel i) := fun i =>
  if hmid : i.val.1 = middle A p hq then
    if hact : i.val.2 ∈ activeSlots p q then
      if i.val.2 ∈ s then
        some ⟨(fun j => p j.val), by
          intro h
          obtain ⟨j, hj, hne⟩ := active_contains_nonidentity p hq i.val.2 hact
          have hm : j ∈ supportAt L i.val := by
            change j ∈ ((L).get i.val.1).support i.val.2
            rw [hmid, midpoint_get]
            exact hj
          exact hne (congrFun h ⟨j, hm⟩)⟩
      else none
    else none
  else none

private theorem subsetHistory_faults_iff (s : Finset (Fin n)) (i : Location L) :
    i ∈ faults (subsetHistory A p hq s) ↔
      i.val.1 = middle A p hq ∧ i.val.2 ∈ activeSlots p q ∧ i.val.2 ∈ s := by
  by_cases hj : i.val.1 = middle A p hq <;>
    by_cases ha : i.val.2 ∈ activeSlots p q <;>
    by_cases hs : i.val.2 ∈ s <;>
    simp [faults, subsetHistory, hj, ha, hs]

private theorem subsetHistory_faults_card (s : Finset (Fin n)) (hs : s ⊆ activeSlots p q) :
    (faults (subsetHistory A p hq s)).card = s.card := by
  apply Finset.card_bij (fun i _ => i.val.2)
  · intro i hi
    exact ((subsetHistory_faults_iff A p hq s i).mp hi).2.2
  · intro i hi j hj hij
    have hi' := ((subsetHistory_faults_iff A p hq s i).mp hi).1
    have hj' := ((subsetHistory_faults_iff A p hq s j).mp hj).1
    exact Subtype.ext (Prod.ext (hi'.trans hj'.symm) hij)
  · intro i hi
    let l := middleLocation A p hq i (hs hi)
    exact ⟨l, (subsetHistory_faults_iff A p hq s l).mpr ⟨rfl, hs hi, hi⟩, rfl⟩

private theorem subsetHistory_middle_label (s : Finset (Fin n)) (i : Location L)
    (hi : i ∈ faults (subsetHistory A p hq s)) :
    outputFault (insertion L) physicalFault (subsetHistory A p hq s) i =
      propagate (layerSequenceEval (A.reverse.map Layer.adjoint)) (blockPauli p q hq i.val.2) := by
  obtain ⟨hj, ha, hs⟩ := (subsetHistory_faults_iff A p hq s i).mp hi
  unfold outputFault subsetHistory
  simp only [dif_pos hj, dif_pos ha, if_pos hs, Option.elim_some]
  change propagate (layerSequenceEval ((L).drop (i.val.1.val + 1)))
    (pauliMatrix 0 (extendLocalPauli (supportAt L i.val) (fun j => p j.val))) = _
  rw [show i.val.1.val = (middle A p hq).val from congrArg Fin.val hj, midpoint_after A p hq]
  congr 1
  unfold blockPauli
  congr 1
  funext x
  have hsupp : supportAt L i.val = (M).support i.val.2 := by
    change ((L).get i.val.1).support i.val.2 = _
    rw [hj, midpoint_get]
  by_cases hx : x ∈ (M).support i.val.2
  · have hx' : x ∈ supportAt L i.val := hsupp.symm ▸ hx
    simp [extendLocalPauli, maskPauli, hx, hx']
  · have hx' : x ∉ supportAt L i.val := hsupp.symm ▸ hx
    simp [extendLocalPauli, maskPauli, hx, hx']

/-- The product of exactly the selected midpoint gate faults before
propagation to the output. Their supports are disjoint. -/
private theorem subsetHistory_propagates (s : Finset (Fin n)) (hs : s ⊆ activeSlots p q) :
    outputHistory (insertion L) physicalFault (subsetHistory A p hq s)
      (chronologicalFaults (subsetHistory A p hq s)) =
      propagate (layerSequenceEval (A.reverse.map Layer.adjoint)) (partialMidpoint p q hq s) := by
  classical
  let x := subsetHistory A p hq s
  let B := chronologicalFaults x
  let indices := (List.finRange n).reverse.filter fun i => decide (i ∈ s)
  let slot : Location L → Fin n := fun i => i.val.2
  let U := layerSequenceEval (A.reverse.map Layer.adjoint)
  have hU : IsUnitary U := layerSequenceEval_isUnitary _
  have hB (i) (hi : i ∈ B) := mem_chronologicalFaults x i hi
  have hslots : List.Perm (B.map slot) indices := by
    apply (List.perm_ext_iff_of_nodup _ _).mpr
    rotate_left
    · apply List.Nodup.map_on
      · intro i hi j hj hij
        have hi' := ((subsetHistory_faults_iff A p hq s i).mp (hB i hi)).1
        have hj' := ((subsetHistory_faults_iff A p hq s j).mp (hB j hj)).1
        exact Subtype.ext (Prod.ext (hi'.trans hj'.symm) hij)
      · exact (fullOrder_nodup L).filter _
    · exact ((List.nodup_reverse.mpr (List.nodup_finRange n)).filter _)
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hm := ((subsetHistory_faults_iff A p hq s j).mp (hB j hj)).2.2
      simp only [indices, List.mem_filter, List.mem_reverse, List.mem_finRange, true_and,
        decide_eq_true_eq]
      exact hm
    · intro hi
      have hm : i ∈ s := by simpa [indices] using hi
      let loc := middleLocation A p hq i (hs hm)
      have hmem : loc ∈ faults x :=
        (subsetHistory_faults_iff A p hq s loc).mpr ⟨rfl, hs hm, hm⟩
      exact List.mem_map.mpr ⟨loc,
        List.mem_filter.mpr ⟨mem_fullOrder L loc, decide_eq_true hmem⟩, rfl⟩
  have hcomm : (indices.map (blockPauli p q hq)).Pairwise Commute := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp
      (fun {i j} hij => (blockPauli_supported p q hq i).commute
        (blockPauli_supported p q hq j) ((M).disjoint i j hij))
    exact ((List.nodup_reverse.mpr (List.nodup_finRange n)).filter _)
  have hperm := ((hslots.map (blockPauli p q hq)).symm.prod_eq' hcomm).symm
  rw [List.map_map] at hperm
  have hpartial : (indices.map (blockPauli p q hq)).prod = partialMidpoint p q hq s := by
    unfold partialMidpoint indices
    rw [List.ofFn_eq_map, ← List.map_reverse]
    exact list_prod_filter_ite (fun i => i ∈ s) _ _
  have hprop (l : List (Operator (QubitBasis n))) :
      (l.map (propagate U)).prod = propagate U l.prod := by
    induction l with
    | nil =>
      change 1 = propagate U 1
      unfold propagate
      rw [Matrix.mul_one]
      exact hU.2.symm
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, ih, propagate_mul _ _ _ hU]
  calc
    _ = ((B.map (blockPauli p q hq ∘ slot)).map (propagate U)).prod := by
      unfold outputHistory
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact subsetHistory_middle_label A p hq s i (hB i hi)
    _ = propagate U (B.map (blockPauli p q hq ∘ slot)).prod := hprop _
    _ = _ := by rw [hperm, hpartial]

theorem perCodeExponent_ceiling {k d h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstabilizer : IsStabilizer C)
    (hdistance : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    perCodeExponent C q h ≤ (upperEnvelope q d h : ℕ∞) := by
  classical
  obtain ⟨A, p, s, t, W, hL, hEval, hcnt, hdis, hcover, htr, hW, hamb⟩ :=
    FaultUpperWitness.exists_midpoint_ambiguous_branches C hstabilizer hdistance q h hq hh
  have hq' : 1 ≤ q := by omega
  let layers := midpointCircuit A p hq'
  let μ := uniformLaw layers
  have hI : Implements C (layerSequenceEval layers) (1 : Operator (Fin (2 ^ k))) := by
    refine ⟨isUnitary_one, 1, isUnitary_one, ?_⟩
    rw [hEval, Matrix.one_kronecker_one, Matrix.one_mul, Matrix.mul_one]
  let e : Experiment C q h := ⟨layers, hL, 1, hI, μ⟩
  apply (iInf_le _ e).trans
  change FaultExponent.exponent (circuitInfidelity C layers μ) ≤ _
  have hs : s ⊆ activeSlots p q := fun i hi => hcover ▸ Finset.mem_union_left t hi
  have ht : t ⊆ activeSlots p q := fun i hi => hcover ▸ Finset.mem_union_right s hi
  let x := subsetHistory A p hq' s
  let y := subsetHistory A p hq' t
  have hx := subsetHistory_faults_card A p hq' s hs
  have hy := subsetHistory_faults_card A p hq' t ht
  have hxy : x ≠ y := by
    intro heq
    have hst : s = t := by
      ext i
      constructor <;> intro hi
      · let l := middleLocation A p hq' i (hs hi)
        have hl := (subsetHistory_faults_iff A p hq' s l).mpr ⟨rfl, hs hi, hi⟩
        rw [show subsetHistory A p hq' s = subsetHistory A p hq' t from heq] at hl
        exact ((subsetHistory_faults_iff A p hq' t l).mp hl).2.2
      · let l := middleLocation A p hq' i (ht hi)
        have hl := (subsetHistory_faults_iff A p hq' t l).mpr ⟨rfl, ht hi, hi⟩
        rw [← show subsetHistory A p hq' s = subsetHistory A p hq' t from heq] at hl
        exact ((subsetHistory_faults_iff A p hq' s l).mp hl).2.2
    subst t
    have hz : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi =>
      Finset.disjoint_left.mp hdis hi hi
    have hp : 0 < upperEnvelope q d h := ceilDiv_pos (by omega) _
    rw [hz] at hcnt
    simp at hcnt
    omega
  have hWtp : (W ⊗ₖ (1 : Operator (Fin 1))) *
      (W ⊗ₖ (1 : Operator (Fin 1))).conjTranspose = 1 :=
    (point_kronecker_isUnitary W 1 hW isUnitary_one).2
  have hWt : Matrix.trace (W ⊗ₖ (1 : Operator (Fin 1))) = 0 := by
    rw [Matrix.trace_kronecker, htr, zero_mul]
  have ha : encodedBranch C y = encodedBranch C x * (W ⊗ₖ (1 : Operator (Fin 1))) := by
    unfold encodedBranch x y
    rw [subsetHistory_propagates A p hq' t ht, subsetHistory_propagates A p hq' s hs]
    exact hamb
  have hbound := ambiguous_exponent_of_traceless_unitary μ (encodedBranch C)
    (encodedBranch_isometry C) x y hxy (W ⊗ₖ (1 : Operator (Fin 1))) hWtp hWt ha
  change (faults x).card = s.card at hx
  change (faults y).card = t.card at hy
  rw [hx, hy, hcnt] at hbound
  exact hbound

theorem stabilizer_perCodeExponent_envelopes {k d h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstabilizer : IsStabilizer C)
    (hdistance : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    (lowerEnvelope q d h : ℕ∞) ≤ perCodeExponent C q h ∧
      perCodeExponent C q h ≤ (upperEnvelope q d h : ℕ∞) :=
  ⟨perCodeExponent_floor C q d h (by omega) hdistance.1,
    perCodeExponent_ceiling C hstabilizer hdistance hd hq hh⟩

#print axioms perCodeExponent_ceiling
#print axioms stabilizer_perCodeExponent_envelopes

end
end CriticalDepth.FaultNativeCeiling
