import FaultNativeModel

/-! Histories confined to one native layer, with arbitrary supported Pauli words. -/

namespace CriticalDepth.FaultNativeModel

open CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.IndependentFaultHistories
open scoped BigOperators

noncomputable section
variable {n q : ℕ}

variable (A : Layers n q) (M : Layer n (fun _ => 2) q) (B : Layers n q)
variable (p : Fin n → SinglePauli) (slots : Finset (Fin n))
variable (hactive : ∀ i ∈ slots, ∃ j ∈ M.support i, p j ≠ .I)

local notation "L" => (A ++ M :: B)

private def middle : Fin (L).length :=
  ⟨A.length, by simp⟩

private theorem middle_get :
    (L).get (middle A M B) = M := by
  change (A ++ M :: B)[A.length] = M
  simp

private theorem middle_after :
    (L).drop ((middle A M B).val + 1) = B := by
  simp [middle, List.drop_append]

def layerPauliWord (M : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli)
    (i : Fin n) : Operator (QubitBasis n) :=
  pauliMatrix 0 (maskPauli p (M.support i))

def selectedLayerPaulis (M : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli)
    (s : Finset (Fin n)) : Operator (QubitBasis n) :=
  (List.ofFn fun i => if i ∈ s then layerPauliWord M p i else 1).reverse.prod

private theorem list_prod_filter_ite {ι M : Type*} [Monoid M]
    (T : ι → Prop) [DecidablePred T] (f : ι → M) (l : List ι) :
    ((l.filter fun i => decide (T i)).map f).prod =
      (l.map fun i => if T i then f i else 1).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : T i <;> simp [hi, ih]

private def middlePauliLocation (i : Fin n) (hi : i ∈ slots) : Location L :=
  ⟨(middle A M B, i), by
    obtain ⟨j, hj, _⟩ := hactive i hi
    exact ⟨j, by simpa only [supportAt, middle_get A M B] using hj⟩⟩

def middlePauliHistory (s : Finset (Fin n)) :
    History (fun i : Location L => FaultLabel i) := fun i =>
  if hmid : i.val.1 = middle A M B then
    if hact : i.val.2 ∈ slots then
      if i.val.2 ∈ s then
        some ⟨(fun j => p j.val), by
          intro h
          obtain ⟨j, hj, hne⟩ := hactive i.val.2 hact
          have hm : j ∈ supportAt L i.val := by
            change j ∈ ((L).get i.val.1).support i.val.2
            rw [hmid, middle_get]
            exact hj
          exact hne (congrFun h ⟨j, hm⟩)⟩
      else none
    else none
  else none

theorem middlePauliHistory_faults_iff (s : Finset (Fin n)) (i : Location L) :
    i ∈ faults (middlePauliHistory A M B p slots hactive s) ↔
      i.val.1 = middle A M B ∧ i.val.2 ∈ slots ∧ i.val.2 ∈ s := by
  by_cases hj : i.val.1 = middle A M B <;>
    by_cases ha : i.val.2 ∈ slots <;>
    by_cases hs : i.val.2 ∈ s <;>
    simp [faults, middlePauliHistory, hj, ha, hs]

theorem middlePauliHistory_faults_card (s : Finset (Fin n)) (hs : s ⊆ slots) :
    (faults (middlePauliHistory A M B p slots hactive s)).card = s.card := by
  apply Finset.card_bij (fun i _ => i.val.2)
  · intro i hi
    exact ((middlePauliHistory_faults_iff A M B p slots hactive s i).mp hi).2.2
  · intro i hi j hj hij
    have hi' := ((middlePauliHistory_faults_iff A M B p slots hactive s i).mp hi).1
    have hj' := ((middlePauliHistory_faults_iff A M B p slots hactive s j).mp hj).1
    exact Subtype.ext (Prod.ext (hi'.trans hj'.symm) hij)
  · intro i hi
    let l := middlePauliLocation A M B p slots hactive i (hs hi)
    exact ⟨l, (middlePauliHistory_faults_iff A M B p slots hactive s l).mpr ⟨rfl, hs hi, hi⟩, rfl⟩

private theorem middlePauliHistory_middle_label (s : Finset (Fin n)) (i : Location L)
    (hi : i ∈ faults (middlePauliHistory A M B p slots hactive s)) :
    outputFault (insertion L) physicalFault (middlePauliHistory A M B p slots hactive s) i =
      propagate (layerSequenceEval B) (layerPauliWord M p i.val.2) := by
  obtain ⟨hj, ha, hs⟩ := (middlePauliHistory_faults_iff A M B p slots hactive s i).mp hi
  unfold outputFault middlePauliHistory
  simp only [dif_pos hj, dif_pos ha, if_pos hs, Option.elim_some]
  change propagate (layerSequenceEval ((L).drop (i.val.1.val + 1)))
    (pauliMatrix 0 (extendLocalPauli (supportAt L i.val) (fun j => p j.val))) = _
  rw [show i.val.1.val = (middle A M B).val from congrArg Fin.val hj, middle_after A M B]
  congr 1
  unfold layerPauliWord
  congr 1
  funext x
  have hsupp : supportAt L i.val = (M).support i.val.2 := by
    change ((L).get i.val.1).support i.val.2 = _
    rw [hj, middle_get]
  by_cases hx : x ∈ (M).support i.val.2
  · have hx' : x ∈ supportAt L i.val := hsupp.symm ▸ hx
    simp [extendLocalPauli, maskPauli, hx, hx']
  · have hx' : x ∉ supportAt L i.val := hsupp.symm ▸ hx
    simp [extendLocalPauli, maskPauli, hx, hx']

/-- The product of exactly the selected midpoint gate faults before
propagation to the output. Their supports are disjoint. -/
theorem middlePauliHistory_propagates (s : Finset (Fin n)) (hs : s ⊆ slots) :
    outputHistory (insertion L) physicalFault (middlePauliHistory A M B p slots hactive s)
      (chronologicalFaults (middlePauliHistory A M B p slots hactive s)) =
      propagate (layerSequenceEval B) (selectedLayerPaulis M p s) := by
  classical
  let x := middlePauliHistory A M B p slots hactive s
  let ordered := chronologicalFaults x
  let indices := (List.finRange n).reverse.filter fun i => decide (i ∈ s)
  let slot : Location L → Fin n := fun i => i.val.2
  let U := layerSequenceEval B
  have hU : IsUnitary U := layerSequenceEval_isUnitary _
  have hB (i) (hi : i ∈ ordered) := mem_chronologicalFaults x i hi
  have hslots : List.Perm (ordered.map slot) indices := by
    apply (List.perm_ext_iff_of_nodup _ _).mpr
    rotate_left
    · apply List.Nodup.map_on
      · intro i hi j hj hij
        have hi' := ((middlePauliHistory_faults_iff A M B p slots hactive s i).mp (hB i hi)).1
        have hj' := ((middlePauliHistory_faults_iff A M B p slots hactive s j).mp (hB j hj)).1
        exact Subtype.ext (Prod.ext (hi'.trans hj'.symm) hij)
      · exact (fullOrder_nodup L).filter _
    · exact ((List.nodup_reverse.mpr (List.nodup_finRange n)).filter _)
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hm := ((middlePauliHistory_faults_iff A M B p slots hactive s j).mp (hB j hj)).2.2
      simp only [indices, List.mem_filter, List.mem_reverse, List.mem_finRange, true_and,
        decide_eq_true_eq]
      exact hm
    · intro hi
      have hm : i ∈ s := by simpa [indices] using hi
      let loc := middlePauliLocation A M B p slots hactive i (hs hm)
      have hmem : loc ∈ faults x :=
        (middlePauliHistory_faults_iff A M B p slots hactive s loc).mpr ⟨rfl, hs hm, hm⟩
      exact List.mem_map.mpr ⟨loc,
        List.mem_filter.mpr ⟨mem_fullOrder L loc, decide_eq_true hmem⟩, rfl⟩
  have hcomm : (indices.map (layerPauliWord M p)).Pairwise Commute := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp
      (fun {i j} hij => (maskPauli_supportedOn p (M.support i)).commute
        (maskPauli_supportedOn p (M.support j)) ((M).disjoint i j hij))
    exact ((List.nodup_reverse.mpr (List.nodup_finRange n)).filter _)
  have hperm := ((hslots.map (layerPauliWord M p)).symm.prod_eq' hcomm).symm
  rw [List.map_map] at hperm
  have hpartial : (indices.map (layerPauliWord M p)).prod = selectedLayerPaulis M p s := by
    unfold selectedLayerPaulis indices
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
    _ = ((ordered.map (layerPauliWord M p ∘ slot)).map (propagate U)).prod := by
      unfold outputHistory
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact middlePauliHistory_middle_label A M B p slots hactive s i (hB i hi)
    _ = propagate U (ordered.map (layerPauliWord M p ∘ slot)).prod := hprop _
    _ = _ := by rw [hperm, hpartial]


#print axioms middlePauliHistory_propagates
#print axioms middlePauliHistory_faults_card

end
end CriticalDepth.FaultNativeModel
