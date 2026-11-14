import FaultHistoryNormalization

/-!
# Actual X-fault histories in a selected native layer

Each selected nonempty gate fails with the full X word on its support. The
output error is the X word on the union of the selected supports, conjugated
by the suffix of the circuit.
-/

namespace CriticalDepth.ShorFaultWitness

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryNormalization CriticalDepth.IndependentFaultHistories
open scoped BigOperators

variable {n q : ℕ}

def fullX (s : Finset (Fin n)) : Operator (QubitBasis n) :=
  pauliMatrix 0 (maskPauli (fun _ => .X) s)

private def localFullX {L : Layers n q} (i : Location L) : FaultLabel i :=
  ⟨fun _ => .X, by
    intro h
    obtain ⟨j, hj⟩ := i.property
    have heq := congrFun h ⟨j, hj⟩
    cases heq⟩

def singleLayerXHistory (L : Layers n q) (ell : Fin L.length) (s : Finset (Fin n)) :
    History (fun i : Location L => FaultLabel i) :=
  fun i => if i.val.1 = ell ∧ i.val.2 ∈ s then some (localFullX i) else none

theorem singleLayerXHistory_faults_iff (L : Layers n q)
    (ell : Fin L.length) (s : Finset (Fin n)) (i : Location L) :
    i ∈ faults (singleLayerXHistory L ell s) ↔ i.val.1 = ell ∧ i.val.2 ∈ s := by
  by_cases hi : i.val.1 = ell ∧ i.val.2 ∈ s <;> simp [faults, singleLayerXHistory, hi]

private def atSlot (L : Layers n q) (ell : Fin L.length) (i : Fin n)
    (hne : ((L.get ell).support i).Nonempty) : Location L :=
  ⟨(ell, i), hne⟩

theorem singleLayerXHistory_faults_card (L : Layers n q) (ell : Fin L.length)
    (s : Finset (Fin n)) (hne : ∀ i ∈ s, ((L.get ell).support i).Nonempty) :
    (faults (singleLayerXHistory L ell s)).card = s.card := by
  apply Finset.card_bij (fun i _ => i.val.2)
  · intro i hi
    exact ((singleLayerXHistory_faults_iff L ell s i).mp hi).2
  · intro i hi j hj hij
    have hi' := ((singleLayerXHistory_faults_iff L ell s i).mp hi).1
    have hj' := ((singleLayerXHistory_faults_iff L ell s j).mp hj).1
    exact Subtype.ext (Prod.ext (hi'.trans hj'.symm) hij)
  · intro i hi
    let loc := atSlot L ell i (hne i hi)
    exact ⟨loc, (singleLayerXHistory_faults_iff L ell s loc).mpr ⟨rfl, hi⟩, rfl⟩

private theorem singleLayerXHistory_outputFault (L : Layers n q) (ell : Fin L.length)
    (s : Finset (Fin n)) (i : Location L) (hi : i ∈ faults (singleLayerXHistory L ell s)) :
    outputFault (insertion L) physicalFault (singleLayerXHistory L ell s) i =
      propagate (layerSequenceEval (L.drop (ell.val + 1))) (fullX ((L.get ell).support i.val.2)) := by
  have hf := (singleLayerXHistory_faults_iff L ell s i).mp hi
  unfold outputFault singleLayerXHistory
  simp only [ite_eq_left hf, Option.elim_some]
  change propagate (layerSequenceEval (L.drop (i.val.1.val + 1)))
    (pauliMatrix 0 (extendLocalPauli (supportAt L i.val) (fun _ => .X))) = _
  have hs : supportAt L i.val = (L.get ell).support i.val.2 := by
    unfold supportAt
    rw [hf.1]
  rw [show i.val.1.val = ell.val from congrArg Fin.val hf.1]
  congr 1
  unfold fullX
  congr 1
  funext j
  by_cases hj : j ∈ (L.get ell).support i.val.2
  · have hj' : j ∈ supportAt L i.val := hs.symm ▸ hj
    simpa [extendLocalPauli, maskPauli, hj'] using hj
  · have hj' : j ∉ supportAt L i.val := hs.symm ▸ hj
    simpa [extendLocalPauli, maskPauli, hj'] using hj

private theorem fullX_eq_one : fullX (∅ : Finset (Fin n)) = 1 := by
  rw [fullX, maskPauli_empty, pauliMatrix_zero_eq_tensorEntries]
  exact map_one (tensorEntriesMonoidHom (Fin n))

private theorem maskFullX_of_subset {S T : Finset (Fin n)} (h : S ⊆ T) :
    maskPauli (maskPauli (fun _ => .X) T) S = maskPauli (fun _ => .X) S := by
  funext j
  by_cases hj : j ∈ S
  · simp [maskPauli, hj, h hj]
  · simp [maskPauli, hj]

private theorem list_prod_filter_ite {ι M : Type*} [Monoid M]
    (T : ι → Prop) [DecidablePred T] (f : ι → M) (l : List ι) :
    ((l.filter fun i => decide (T i)).map f).prod =
      (l.map fun i => if T i then f i else 1).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      by_cases hi : T i <;> simp [hi, ih]

private theorem selectedSlots_prod (A : Layer n (fun _ => 2) q) (s : Finset (Fin n)) :
    (((List.finRange n).filter fun i => decide (i ∈ s)).map fun i => fullX (A.support i)).prod =
      fullX (s.biUnion A.support) := by
  classical
  let blocks (i : Fin n) := if i ∈ s then A.support i else ∅
  have hdis (i j : Fin n) (hij : i ≠ j) : Disjoint (blocks i) (blocks j) := by
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [blocks, hi, hj, A.disjoint i j hij]
  have hsub (i : Fin n) : blocks i ⊆ s.biUnion A.support := by
    intro j hj
    by_cases hi : i ∈ s
    · exact Finset.mem_biUnion.mpr ⟨i, hi, by simpa [blocks, hi] using hj⟩
    · simp [blocks, hi] at hj
  have hcover (j : Fin n)
      (hj : j ∈ pauliSupport (maskPauli (fun _ => .X) (s.biUnion A.support))) :
      ∃ i, j ∈ blocks i := by
    have hj' : j ∈ s.biUnion A.support := by
      by_contra hn
      change j ∈ Finset.univ.filter
        (fun k => maskPauli (fun _ => .X) (s.biUnion A.support) k ≠ .I) at hj
      have hne := (Finset.mem_filter.mp hj).2
      exact hne (ite_eq_right hn)
    obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj'
    exact ⟨i, by simpa [blocks, hi] using hji⟩
  have hmatrix := pauliMatrix_eq_masked_product _ blocks hdis hcover
  simp only [maskFullX_of_subset (hsub _)] at hmatrix
  unfold fullX
  rw [hmatrix, List.ofFn_eq_map, list_prod_filter_ite]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i ∈ s
  · simp [blocks, hi]
  · have h := fullX_eq_one (n := n)
    simpa only [blocks, hi, ite_false, fullX] using h.symm

/-- A single noisy layer, with all other locations clean, gives an exact
output-frame suffix conjugation of the full X word on the selected support. -/
theorem singleLayerXHistory_output (L : Layers n q) (ell : Fin L.length)
    (s : Finset (Fin n)) (hne : ∀ i ∈ s, ((L.get ell).support i).Nonempty) :
    outputHistory (insertion L) physicalFault (singleLayerXHistory L ell s)
      (chronologicalFaults (singleLayerXHistory L ell s)) =
      propagate (layerSequenceEval (L.drop (ell.val + 1))) (fullX (s.biUnion (L.get ell).support)) := by
  classical
  let x := singleLayerXHistory L ell s
  let B := chronologicalFaults x
  let indices := (List.finRange n).filter fun i => decide (i ∈ s)
  let slot : Location L → Fin n := fun i => i.val.2
  let U := layerSequenceEval (L.drop (ell.val + 1))
  let F : Fin n → Operator (QubitBasis n) := fun i => fullX ((L.get ell).support i)
  have hU : IsUnitary U := layerSequenceEval_isUnitary _
  have hB (i) (hi : i ∈ B) := mem_chronologicalFaults x i hi
  have hslots : List.Perm (B.map slot) indices := by
    apply (List.perm_ext_iff_of_nodup _ _).mpr
    rotate_left
    · apply List.Nodup.map_on
      · intro i hi j hj hij
        have hi' := ((singleLayerXHistory_faults_iff L ell s i).mp (hB i hi)).1
        have hj' := ((singleLayerXHistory_faults_iff L ell s j).mp (hB j hj)).1
        exact Subtype.ext (Prod.ext (hi'.trans hj'.symm) hij)
      · exact (fullOrder_nodup L).filter _
    · exact (List.nodup_finRange _).filter _
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hm := ((singleLayerXHistory_faults_iff L ell s j).mp (hB j hj)).2
      simpa [indices, slot] using hm
    · intro hi
      have hm : i ∈ s := by simpa [indices] using hi
      let loc := atSlot L ell i (hne i hm)
      have hl : loc ∈ faults x := (singleLayerXHistory_faults_iff L ell s loc).mpr ⟨rfl, hm⟩
      exact List.mem_map.mpr ⟨loc,
        List.mem_filter.mpr ⟨mem_fullOrder L loc, decide_eq_true hl⟩, rfl⟩
  have hcomm : (indices.map F).Pairwise Commute := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp
      (fun {i j} hij => (maskPauli_supportedOn (fun _ => .X) ((L.get ell).support i)).commute
        (maskPauli_supportedOn (fun _ => .X) ((L.get ell).support j)) ((L.get ell).disjoint i j hij))
    exact (List.nodup_finRange _).filter _
  have hperm := ((hslots.map F).symm.prod_eq' hcomm).symm
  rw [List.map_map] at hperm
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
    _ = ((B.map (F ∘ slot)).map (propagate U)).prod := by
      unfold outputHistory
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact singleLayerXHistory_outputFault L ell s i (hB i hi)
    _ = propagate U (B.map (F ∘ slot)).prod := hprop _
    _ = _ := by
      rw [hperm]
      congr 1
      exact selectedSlots_prod (L.get ell) s

theorem normalized_support_of_gate_mem (A : PaperLayer (n := n) (q := q))
    (g : Gate (n := n) (q := q)) (hg : g ∈ A.gates) (hne : g.support.Nonempty) :
    ∃ i : Fin n, A.normalized.support i = g.support := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
  let k : {j : Fin A.gates.length // (A.gates.get j).support.Nonempty} :=
    ⟨j, by rw [hj]; exact hne⟩
  refine ⟨(layerLocationEquiv A k).val, ?_⟩
  exact (layerLocationEquiv_support A k).trans (congrArg ListGate.support hj)

/-- A finite collection of pairwise disjoint, nonempty desired supports
determines a history with exactly one full X fault on each corresponding gate. -/
theorem exists_singleLayerXHistory_of_supports
    {G : Type*} [Fintype G] (L : Layers n q) (ell : Fin L.length)
    (sites : G → Finset (Fin n)) (hne : ∀ g, (sites g).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (sites a) (sites b))
    (hslots : ∀ g, ∃ i : Fin n, (L.get ell).support i = sites g) :
    ∃ x : History (fun i : Location L => FaultLabel i),
      (∀ i ∈ faults x, i.val.1 = ell) ∧
      (faults x).card = Fintype.card G ∧
      outputHistory (insertion L) physicalFault x (chronologicalFaults x) =
        propagate (layerSequenceEval (L.drop (ell.val + 1))) (fullX (Finset.univ.biUnion sites)) := by
  classical
  choose slot hslot using hslots
  have hinj : Function.Injective slot := by
    intro a b hab
    by_contra hneab
    have hs := hdis a b hneab
    have he : sites a = sites b := (hslot a).symm.trans ((congrArg (L.get ell).support hab).trans (hslot b))
    obtain ⟨j, hj⟩ := hne a
    have hj' : j ∈ sites b := he ▸ hj
    exact Finset.disjoint_left.mp hs hj hj'
  let s : Finset (Fin n) := Finset.univ.map ⟨slot, hinj⟩
  have hs (i : Fin n) (hi : i ∈ s) : ((L.get ell).support i).Nonempty := by
    obtain ⟨g, _, rfl⟩ := Finset.mem_map.mp hi
    change ((L.get ell).support (slot g)).Nonempty
    exact (hslot g).symm ▸ hne g
  have hUnion : s.biUnion (L.get ell).support = Finset.univ.biUnion sites := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
      obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hi
      change j ∈ (L.get ell).support (slot g) at hji
      exact Finset.mem_biUnion.mpr ⟨g, hg, (hslot g) ▸ hji⟩
    · intro hj
      obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp hj
      exact Finset.mem_biUnion.mpr ⟨slot g, Finset.mem_map.mpr ⟨g, hg, rfl⟩, by
        rw [hslot]
        exact hjg⟩
  refine ⟨singleLayerXHistory L ell s, ?_, ?_, ?_⟩
  · intro i hi
    exact ((singleLayerXHistory_faults_iff L ell s i).mp hi).1
  · rw [singleLayerXHistory_faults_card L ell s hs]
    simp [s]
  · rw [singleLayerXHistory_output L ell s hs, hUnion]

#print axioms singleLayerXHistory_faults_iff
#print axioms singleLayerXHistory_faults_card
#print axioms singleLayerXHistory_output
#print axioms normalized_support_of_gate_mem
#print axioms exists_singleLayerXHistory_of_supports

end
end CriticalDepth.ShorFaultWitness
