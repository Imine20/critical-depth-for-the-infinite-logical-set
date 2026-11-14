import NativeMiddlePauliHistory
import FaultUpperWitness

/-! A balanced pair of native midpoint histories for an intended logical Pauli. -/

namespace CriticalDepth.MidpointFaultWitness

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultNativeModel
open CriticalDepth.IndependentFaultHistories CriticalDepth.FaultDepthArithmetic
open scoped BigOperators Kronecker ENat
noncomputable section

variable {n q : ℕ}

def activePauliSlots (M : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x ∈ M.support i, p x ≠ .I

theorem activePauliSlots_spec (M : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli)
    (i : Fin n) (hi : i ∈ activePauliSlots M p) : ∃ x ∈ M.support i, p x ≠ .I :=
  (Finset.mem_filter.mp hi).2

private theorem layerPauliWord_one_of_inactive (M : Layer n (fun _ => 2) q)
    (p : Fin n → SinglePauli) (i : Fin n) (hi : i ∉ activePauliSlots M p) :
    layerPauliWord M p i = 1 := by
  have he : maskPauli p (M.support i) = fun _ => .I := by
    funext x
    by_cases hx : x ∈ M.support i
    · have hn : p x = .I := by
        by_contra h
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, h⟩)
      simp [maskPauli, hx, hn]
    · simp [maskPauli, hx]
  rw [layerPauliWord, he, pauliMatrix_zero_eq_tensorEntries]
  exact map_one (tensorEntriesMonoidHom (Fin n))

private theorem selectedLayerPaulis_mul_complement
    (M : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli)
    (hcover : ∀ x ∈ pauliSupport p, ∃ i, x ∈ M.support i)
    (s : Finset (Fin n)) (hs : s ⊆ activePauliSlots M p) :
    selectedLayerPaulis M p s * selectedLayerPaulis M p (activePauliSlots M p \ s) =
      pauliMatrix 0 p := by
  classical
  let f i := if i ∈ s then layerPauliWord M p i else 1
  let g i := if i ∈ activePauliSlots M p \ s then layerPauliWord M p i else 1
  have hc (i j : Fin n) : Commute (g i) (f j) := by
    by_cases hi : i ∈ activePauliSlots M p \ s <;> by_cases hj : j ∈ s
    · have hne : i ≠ j := fun h => (Finset.mem_sdiff.mp hi).2 (h.symm ▸ hj)
      simpa only [g, f, if_pos hi, if_pos hj, layerPauliWord] using
        (maskPauli_supportedOn p (M.support i)).commute (maskPauli_supportedOn p (M.support j))
          (M.disjoint i j hne)
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
  have hsingle (i : Fin n) : f i * g i = layerPauliWord M p i := by
    by_cases hi : i ∈ s
    · simp [f, g, hi]
    · by_cases hit : i ∈ activePauliSlots M p
      · simp [f, g, hi, hit]
      · simp [f, g, hi, hit, layerPauliWord_one_of_inactive M p i hit]
  have heq := hprod (List.ofFn (fun i : Fin n => i)).reverse
  simp only [List.map_reverse, List.map_ofFn, Function.comp_def, hsingle] at heq
  have hp : (List.ofFn (layerPauliWord M p)).Pairwise Commute := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact (maskPauli_supportedOn p _).commute (maskPauli_supportedOn p _)
      (M.disjoint _ _ (fun he => (Nat.ne_of_lt hij) (congrArg Fin.val he)))
  exact heq.trans (((List.reverse_perm _).symm.prod_eq' hp).symm.trans
    (pauliMatrix_eq_masked_product p M.support M.disjoint hcover).symm)

private theorem selectedLayerPaulis_sq (M : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli)
    (s : Finset (Fin n)) : selectedLayerPaulis M p s * selectedLayerPaulis M p s = 1 := by
  let P (i : Fin n) := if i ∈ s then layerPauliWord M p i else 1
  have hP (i : Fin n) : P i * P i = 1 := by
    by_cases hi : i ∈ s
    · simpa only [P, if_pos hi, layerPauliWord] using unphased_pauliMatrix_sq (maskPauli p (M.support i))
    · simp [P, hi]
  have hSupp (i : Fin n) : SupportedOn (P i) (M.support i) := by
    by_cases hi : i ∈ s
    · simpa only [P, if_pos hi, layerPauliWord] using maskPauli_supportedOn p (M.support i)
    · simpa only [P, if_neg hi] using supportedOn_one (M.support i)
  let L : Layer n (fun _ => 2) q :=
    { M with
      gate := P
      locality := hSupp
      unitary := fun i => by
        by_cases hi : i ∈ s
        · simpa only [P, if_pos hi, layerPauliWord] using unphased_pauliMatrix_isUnitary (maskPauli p (M.support i))
        · simpa only [P, if_neg hi] using (isUnitary_one (ι := QubitBasis n)) }
  have he := layerEval_withPostGateFaults L P hSupp
  change (List.ofFn fun i => P i * P i).reverse.prod =
    selectedLayerPaulis M p s * selectedLayerPaulis M p s at he
  rw [← he]
  simp only [hP, List.ofFn_const, List.reverse_replicate, List.prod_replicate, one_pow]

theorem exists_native_midpoint_histories
    {K : ℕ} (C : Code n (fun _ => 2) K 1)
    (A B : Layers n q) (M : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli)
    (W : Operator (Fin K)) (w : ℕ) (hw : 0 < w)
    (hcover : ∀ x ∈ pauliSupport p, ∃ i, x ∈ M.support i)
    (hcount : (activePauliSlots M p).card = w)
    (hAction : propagate (layerSequenceEval B) (pauliMatrix 0 p) * C.encoding =
      C.encoding * (W ⊗ₖ (1 : Operator (Fin 1)))) :
    let L := A ++ M :: B
    ∃ x y : History (fun i : Location L => FaultLabel i),
      x ≠ y ∧ (faults x).card = w / 2 ∧ (faults y).card = ceilDiv w 2 ∧
      (∀ i ∈ faults x ∪ faults y, i.val.1.val = A.length) ∧
      encodedBranch C y = encodedBranch C x * (W ⊗ₖ (1 : Operator (Fin 1))) := by
  classical
  intro L
  let S := activePauliSlots M p
  have hc : S.card = w := hcount
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := S) (n := w / 2) (by omega)
  let t := S \ s
  have ht : t ⊆ S := Finset.sdiff_subset
  let x := middlePauliHistory A M B p S (activePauliSlots_spec M p) s
  let y := middlePauliHistory A M B p S (activePauliSlots_spec M p) t
  have hx : (faults x).card = s.card := middlePauliHistory_faults_card A M B p S _ s hs
  have hy : (faults y).card = t.card := middlePauliHistory_faults_card A M B p S _ t ht
  have htc : t.card = ceilDiv w 2 := by
    rw [show t.card = S.card - s.card from Finset.card_sdiff_of_subset hs,
      hc, hcard, ceilDiv_of_pos hw]
    omega
  have hxy : x ≠ y := by
    intro he
    have hpos : 0 < (faults y).card := by rw [hy, htc]; exact ceilDiv_pos hw _
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    have hi' : i ∈ faults x := he.symm ▸ hi
    have hs' := ((middlePauliHistory_faults_iff A M B p S _ s i).mp hi').2.2
    have ht' := ((middlePauliHistory_faults_iff A M B p S _ t i).mp hi).2.2
    exact (Finset.mem_sdiff.mp ht').2 hs'
  refine ⟨x, y, hxy, hx.trans hcard, hy.trans htc, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact congrArg Fin.val ((middlePauliHistory_faults_iff A M B p S _ s i).mp h).1
    · exact congrArg Fin.val ((middlePauliHistory_faults_iff A M B p S _ t i).mp h).1
  · let U := layerSequenceEval B
    let F := propagate U (selectedLayerPaulis M p s)
    let G := propagate U (selectedLayerPaulis M p t)
    have hu : IsUnitary U := layerSequenceEval_isUnitary _
    have hX : encodedBranch C x = F * C.encoding := by
      unfold encodedBranch x
      rw [middlePauliHistory_propagates A M B p S _ s hs]
    have hY : encodedBranch C y = G * C.encoding := by
      unfold encodedBranch y
      rw [middlePauliHistory_propagates A M B p S _ t ht]
    have hFG : F * G = propagate U (pauliMatrix 0 p) := by
      dsimp only [F, G]
      rw [← propagate_mul _ _ _ hu, selectedLayerPaulis_mul_complement M p hcover s hs]
    have hFF : F * F = 1 := by
      dsimp only [F]
      rw [← propagate_mul _ _ _ hu, selectedLayerPaulis_sq, propagate, Matrix.mul_one]
      exact hu.2
    rw [hX,hY]
    calc
      _ = F * (F * G) * C.encoding := by rw [← mul_assoc, hFF, one_mul]
      _ = _ := by rw [hFG, Matrix.mul_assoc, hAction, ← Matrix.mul_assoc]

#print axioms exists_native_midpoint_histories

end
end CriticalDepth.MidpointFaultWitness
