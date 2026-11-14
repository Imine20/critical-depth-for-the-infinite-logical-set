import FaultNativeModel
import Mathlib.Data.List.NodupEquivFin

/-!
# Normalization of fault locations for finite gate lists

The gate occurrences in each original list are indexed by their original
positions. The normalization retains every occurrence with nonempty support
and preserves its support, ideal gate, and position relative to other
retained gates. Supported identity gates with nonempty support are included.
-/

namespace CriticalDepth.FaultHistoryNormalization

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultCircuitSupport CriticalDepth.IndependentFaultHistories
open scoped BigOperators

variable {n q : ℕ}

abbrev Gate := ListGate n (fun _ => 2) q
abbrev PaperLayer := ArbitraryLayer n (fun _ => 2) q
abbrev PaperLayers := List (PaperLayer (n := n) (q := q))

private theorem filter_sublist (gates : List (Gate (n := n) (q := q))) :
    List.Sublist (filterNonemptyGates gates) gates := by
  induction gates with
  | nil => exact List.Sublist.slnil
  | cons g gs ih =>
    by_cases hg : g.support = ∅
    · simpa only [filterNonemptyGates, if_pos hg] using List.Sublist.cons g ih
    · simpa only [filterNonemptyGates, if_neg hg] using List.Sublist.cons_cons g ih

private def retainedEmbedding (L : PaperLayer (n := n) (q := q)) :
    Fin (filterNonemptyGates L.gates).length ↪o Fin L.gates.length :=
  (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (filter_sublist L.gates)).choose

private theorem retained_get (L : PaperLayer (n := n) (q := q))
    (i : Fin (filterNonemptyGates L.gates).length) :
    (filterNonemptyGates L.gates).get i = L.gates.get (retainedEmbedding L i) :=
  (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (filter_sublist L.gates)).choose_spec i

private theorem get_injective_of_nonempty (L : PaperLayer (n := n) (q := q))
    {i j : Fin L.gates.length} (hi : (L.gates.get i).support.Nonempty)
    (heq : L.gates.get i = L.gates.get j) : i = j := by
  by_contra hne
  have hpair := List.pairwise_iff_getElem.mp L.disjoint
  obtain ⟨a, ha⟩ := hi
  have hb : a ∈ (L.gates.get j).support := by rw [← heq]; exact ha
  rcases lt_or_gt_of_ne hne with h | h
  · have hd := hpair i.val j.val i.isLt j.isLt h
    exact Finset.disjoint_left.mp hd ha hb
  · have hd := hpair j.val i.val j.isLt i.isLt h
    exact Finset.disjoint_left.mp hd hb ha

private def retainedToOriginal (L : PaperLayer (n := n) (q := q))
    (i : Fin (filterNonemptyGates L.gates).length) :
    {j : Fin L.gates.length // (L.gates.get j).support.Nonempty} := by
  refine ⟨retainedEmbedding L i, ?_⟩
  rw [← retained_get L i]
  exact Finset.nonempty_iff_ne_empty.mpr
    ((mem_filterNonemptyGates _ _).mp (List.get_mem _ _)).2

private theorem retainedToOriginal_bijective (L : PaperLayer (n := n) (q := q)) :
    Function.Bijective (retainedToOriginal L) := by
  constructor
  · intro i j h
    exact (retainedEmbedding L).injective (congrArg Subtype.val h)
  · intro j
    have hj' : L.gates.get j.val ∈ filterNonemptyGates L.gates :=
      (mem_filterNonemptyGates _ _).mpr ⟨List.get_mem _ _, j.property.ne_empty⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hj'
    refine ⟨i, Subtype.ext ?_⟩
    exact (get_injective_of_nonempty L j.property
      (hi.symm.trans (retained_get L i))).symm

private theorem normalized_support_left (L : PaperLayer (n := n) (q := q))
    (i : Fin n) (hi : i.val < (filterNonemptyGates L.gates).length) :
    L.normalized.support i = ((filterNonemptyGates L.gates).get ⟨i.val, hi⟩).support := by
  simp only [ArbitraryLayer.normalized, layerOfGateList]
  rw [List.getElem_append_left hi]
  rfl

private theorem normalized_support_right (L : PaperLayer (n := n) (q := q))
    (i : Fin n) (hi : (filterNonemptyGates L.gates).length ≤ i.val) :
    L.normalized.support i = ∅ := by
  simp only [ArbitraryLayer.normalized, layerOfGateList]
  rw [List.getElem_append_right hi, List.getElem_replicate]
  rfl

private def retainedToSlot (L : PaperLayer (n := n) (q := q))
    (i : Fin (filterNonemptyGates L.gates).length) :
    {j : Fin n // (L.normalized.support j).Nonempty} := by
  let j : Fin n := ⟨i.val, i.isLt.trans_le (filterNonemptyGates_length_le L)⟩
  refine ⟨j, ?_⟩
  rw [normalized_support_left L j i.isLt]
  exact Finset.nonempty_iff_ne_empty.mpr
    ((mem_filterNonemptyGates _ _).mp (List.get_mem _ _)).2

private theorem retainedToSlot_bijective (L : PaperLayer (n := n) (q := q)) :
    Function.Bijective (retainedToSlot L) := by
  constructor
  · intro i j h
    exact Fin.ext (congrArg (fun k : {j : Fin n // (L.normalized.support j).Nonempty} =>
      k.val.val) h)
  · intro j
    have hj : j.val.val < (filterNonemptyGates L.gates).length := by
      by_contra hn
      exact j.property.ne_empty (normalized_support_right L j.val (Nat.le_of_not_gt hn))
    exact ⟨⟨j.val.val, hj⟩, Subtype.ext (Fin.ext rfl)⟩

/-- Nonempty original occurrences correspond bijectively to the nonempty slots. -/
def layerLocationEquiv (L : PaperLayer (n := n) (q := q)) :
    {i : Fin L.gates.length // (L.gates.get i).support.Nonempty} ≃
      {j : Fin n // (L.normalized.support j).Nonempty} :=
  (Equiv.ofBijective _ (retainedToOriginal_bijective L)).symm.trans
    (Equiv.ofBijective _ (retainedToSlot_bijective L))

theorem layerLocationEquiv_support (L : PaperLayer (n := n) (q := q))
    (i : {j : Fin L.gates.length // (L.gates.get j).support.Nonempty}) :
    L.normalized.support (layerLocationEquiv L i).val = (L.gates.get i.val).support := by
  obtain ⟨j, rfl⟩ := (retainedToOriginal_bijective L).surjective i
  have he : layerLocationEquiv L (retainedToOriginal L j) = retainedToSlot L j := by
    change (Equiv.ofBijective _ (retainedToSlot_bijective L))
      ((Equiv.ofBijective _ (retainedToOriginal_bijective L)).symm
        ((Equiv.ofBijective _ (retainedToOriginal_bijective L)) j)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [he]
  exact (normalized_support_left L _ j.isLt).trans
    (congrArg ListGate.support (retained_get L j))

/-- Empty supports have no nonidentity Pauli labels. -/
theorem empty_support_no_fault (S : Finset (Fin n)) (hS : S = ∅) :
    IsEmpty {p : S → SinglePauli // p ≠ fun _ => .I} := by
  subst S
  refine ⟨fun p => p.property ?_⟩
  funext j
  exact False.elim (Finset.notMem_empty j.val j.property)

def normalizedLayers (L : PaperLayers (n := n) (q := q)) : Layers n q :=
  L.map ArbitraryLayer.normalized

def paperSequenceEval (L : PaperLayers (n := n) (q := q)) : Operator (QubitBasis n) :=
  (L.map ArbitraryLayer.eval).reverse.prod

private theorem projective_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A A' B B' : Operator ι}
    (hA : ProjectivelyEquivalent A A') (hB : ProjectivelyEquivalent B B') :
    ProjectivelyEquivalent (A * B) (A' * B') := by
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  have h : star (b * a) * (b * a) = 1 := by
    calc
      star (b * a) * (b * a) = (star a * a) * (star b * b) := by rw [star_mul]; ring
      _ = 1 := by rw [ha, hb, one_mul]
  exact ⟨b * a, h, by simp only [smul_mul_assoc, mul_smul_comm, smul_smul]⟩

theorem sequence_normalization_phase (L : PaperLayers (n := n) (q := q)) :
    ProjectivelyEquivalent (paperSequenceEval L) (layerSequenceEval (normalizedLayers L)) := by
  induction L with
  | nil => exact projectivelyEquivalent_refl 1
  | cons l ls ih =>
    have hstep : paperSequenceEval (l :: ls) = paperSequenceEval ls * l.eval := by
      simp [paperSequenceEval, List.reverse_cons, List.prod_append]
    rw [hstep]
    exact projective_mul ih l.normalization_phase

theorem sequence_normalization_conjugation (L : PaperLayers (n := n) (q := q))
    (U : Operator (QubitBasis n)) :
    propagate (paperSequenceEval L) U =
      propagate (layerSequenceEval (normalizedLayers L)) U :=
  projectivelyEquivalent_conjugation_eq (sequence_normalization_phase L) U

abbrev PaperLocation (L : PaperLayers (n := n) (q := q)) :=
  Σ i : Fin L.length, {j : Fin (L.get i).gates.length // ((L.get i).gates.get j).support.Nonempty}

def paperSupport (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) : Finset (Fin n) :=
  ((L.get i.1).gates.get i.2.val).support

abbrev PaperLabel (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :=
  {p : paperSupport L i → SinglePauli // p ≠ fun _ => .I}

private def normalizedLocation (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :
    Location (normalizedLayers L) := by
  let j : Fin (normalizedLayers L).length :=
    ⟨i.1.val, by simpa only [normalizedLayers, List.length_map] using i.1.isLt⟩
  let k := layerLocationEquiv (L.get i.1) i.2
  refine ⟨(j, k.val), ?_⟩
  simpa only [supportAt, normalizedLayers, j, List.get_eq_getElem, List.getElem_map]
    using k.property

private theorem normalizedLocation_bijective (L : PaperLayers (n := n) (q := q)) :
    Function.Bijective (normalizedLocation L) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hval := congrArg (fun z : Location (normalizedLayers L) => z.val.1.val) h
    have hij : i = j := Fin.ext hval
    subst j
    have hslot := congrArg (fun z : Location (normalizedLayers L) => z.val.2) h
    have hab : a = b := (layerLocationEquiv (L.get i)).injective (Subtype.ext hslot)
    subst b
    rfl
  · intro z
    let i : Fin L.length :=
      ⟨z.val.1.val, by simpa only [normalizedLayers, List.length_map] using z.val.1.isLt⟩
    let j : {k : Fin n // ((L.get i).normalized.support k).Nonempty} :=
      ⟨z.val.2, by simpa only [supportAt, normalizedLayers, i, List.get_eq_getElem,
        List.getElem_map] using z.property⟩
    refine ⟨⟨i, (layerLocationEquiv (L.get i)).symm j⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact Fin.ext rfl
    · change (layerLocationEquiv (L.get i) ((layerLocationEquiv (L.get i)).symm j)).val = j.val
      rw [Equiv.apply_symm_apply]

def locationEquiv (L : PaperLayers (n := n) (q := q)) :
    PaperLocation L ≃ Location (normalizedLayers L) :=
  Equiv.ofBijective _ (normalizedLocation_bijective L)

theorem locationEquiv_support (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :
    supportAt (normalizedLayers L) (locationEquiv L i).val = paperSupport L i := by
  change supportAt (normalizedLayers L) (normalizedLocation L i).val = paperSupport L i
  simpa only [normalizedLocation, supportAt, normalizedLayers, List.get_eq_getElem,
    List.getElem_map, paperSupport]
    using layerLocationEquiv_support (L.get i.1) i.2

def labelEquiv (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :
    PaperLabel L i ≃ FaultLabel (locationEquiv L i) :=
  Equiv.cast (congrArg (fun S : Finset (Fin n) => {p : S → SinglePauli // p ≠ fun _ => .I})
    (locationEquiv_support L i).symm)

def paperPhysicalFault (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L)
    (a : PaperLabel L i) : Operator (QubitBasis n) :=
  pauliMatrix 0 (extendLocalPauli (paperSupport L i) a.val)

theorem labelEquiv_physicalFault (L : PaperLayers (n := n) (q := q))
    (i : PaperLocation L) (a : PaperLabel L i) :
    physicalFault (locationEquiv L i) (labelEquiv L i a) = paperPhysicalFault L i a := by
  let f (S : Finset (Fin n)) (x : {p : S → SinglePauli // p ≠ fun _ => .I}) :=
    pauliMatrix 0 (extendLocalPauli S x.val)
  have h (S T : Finset (Fin n)) (hST : S = T)
      (x : {p : S → SinglePauli // p ≠ fun _ => .I}) :
      f T (Equiv.cast (congrArg (fun R : Finset (Fin n) =>
        {p : R → SinglePauli // p ≠ fun _ => .I}) hST) x) = f S x := by subst T; rfl
  exact h _ _ (locationEquiv_support L i).symm a

def historyEquiv (L : PaperLayers (n := n) (q := q)) :
    History (PaperLabel L) ≃ History (fun i : Location (normalizedLayers L) => FaultLabel i) :=
  (locationEquiv L).piCongr (fun i => Equiv.optionCongr (labelEquiv L i))

theorem historyEquiv_apply (L : PaperLayers (n := n) (q := q))
    (x : History (PaperLabel L)) (i : PaperLocation L) :
    historyEquiv L x (locationEquiv L i) = (x i).map (labelEquiv L i) :=
  Equiv.piCongr_apply_apply _ _ _ _

theorem historyEquiv_fault_count (L : PaperLayers (n := n) (q := q))
    (x : History (PaperLabel L)) :
    (faults (historyEquiv L x)).card = (faults x).card := by
  classical
  have hmap : (faults x).map (locationEquiv L).toEmbedding = faults (historyEquiv L x) := by
    ext i
    obtain ⟨j, rfl⟩ := (locationEquiv L).surjective i
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, faults, Finset.mem_filter, Finset.mem_univ, true_and, historyEquiv_apply]
    cases x j <;> simp
  rw [← hmap, Finset.card_map]

def pullLaw (L : PaperLayers (n := n) (q := q))
    (μ : Law (fun i : Location (normalizedLayers L) => FaultLabel i)) : Law (PaperLabel L) where
  weight i a := μ.weight (locationEquiv L i) (labelEquiv L i a)
  positive i a := μ.positive _ _
  normalized i :=
    ((labelEquiv L i).sum_comp (μ.weight (locationEquiv L i))).trans (μ.normalized _)

theorem historyEquiv_mass (L : PaperLayers (n := n) (q := q))
    (μ : Law (fun i : Location (normalizedLayers L) => FaultLabel i))
    (p : ℝ) (x : History (PaperLabel L)) :
    mass μ p (historyEquiv L x) = mass (pullLaw L μ) p x := by
  unfold mass
  rw [← (locationEquiv L).prod_comp (fun i => localMass μ p i (historyEquiv L x i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [historyEquiv_apply]
  cases x i <;> rfl

theorem normalization_probability_sum (L : PaperLayers (n := n) (q := q))
    (μ : Law (fun i : Location (normalizedLayers L) => FaultLabel i)) (p : ℝ)
    (f : History (fun i : Location (normalizedLayers L) => FaultLabel i) → ℝ) :
    (∑ x, mass (pullLaw L μ) p x * f (historyEquiv L x)) = ∑ y, mass μ p y * f y := by
  simp_rw [← historyEquiv_mass]
  exact (historyEquiv L).sum_comp (fun y => mass μ p y * f y)

theorem layerLocationEquiv_lt_iff (L : PaperLayer (n := n) (q := q))
    (i j : {k : Fin L.gates.length // (L.gates.get k).support.Nonempty}) :
    (layerLocationEquiv L i).val < (layerLocationEquiv L j).val ↔ i.val < j.val := by
  obtain ⟨a, rfl⟩ := (retainedToOriginal_bijective L).surjective i
  obtain ⟨b, rfl⟩ := (retainedToOriginal_bijective L).surjective j
  have he (k : Fin (filterNonemptyGates L.gates).length) :
      layerLocationEquiv L (retainedToOriginal L k) = retainedToSlot L k := by
    change (Equiv.ofBijective _ (retainedToSlot_bijective L))
      ((Equiv.ofBijective _ (retainedToOriginal_bijective L)).symm
        ((Equiv.ofBijective _ (retainedToOriginal_bijective L)) k)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  simp only [he]
  change a < b ↔ retainedEmbedding L a < retainedEmbedding L b
  exact (retainedEmbedding L).lt_iff_lt.symm

theorem locationEquiv_layer_index (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :
    (locationEquiv L i).val.1.val = i.1.val := rfl

def paperOrderKey (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :=
  (i.1.val, i.2.val.val)

def nativeOrderKey {L : Layers n q} (i : Location L) :=
  (i.val.1.val, i.val.2.val)

def earlier (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2

private theorem locationEquiv_earlier (L : PaperLayers (n := n) (q := q)) (i j : PaperLocation L) :
    earlier (nativeOrderKey (locationEquiv L i)) (nativeOrderKey (locationEquiv L j)) ↔
      earlier (paperOrderKey L i) (paperOrderKey L j) := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  change (i.val < j.val ∨ i.val = j.val ∧
    (layerLocationEquiv (L.get i) a).val.val < (layerLocationEquiv (L.get j) b).val.val) ↔ _
  by_cases h : i = j
  · subst j
    simpa only [paperOrderKey, earlier, lt_irrefl, false_or, true_and, and_true, Fin.lt_def] using
      layerLocationEquiv_lt_iff (L.get i) a b
  · have h' : i.val ≠ j.val := fun hv => h (Fin.ext hv)
    simp [paperOrderKey, earlier, h']

theorem fullOrder_descending (L : Layers n q) :
    (fullOrder L).Pairwise (fun a b => earlier (nativeOrderKey b) (nativeOrderKey a)) := by
  unfold fullOrder
  rw [List.pairwise_reverse]
  apply List.Pairwise.filterMap
    (R := fun (a b : Fin L.length × Fin n) => earlier (a.1.val, a.2.val) (b.1.val, b.2.val))
  · intro a a' h b hb b' hb'
    have hab (u : Fin L.length × Fin n) (v : Location L)
        (hu : (if h : (supportAt L u).Nonempty then some (⟨u, h⟩ : Location L) else none) = some v) :
        u = v.val := by
      split at hu
      · exact congrArg Subtype.val (Option.some.inj hu)
      · cases hu
    unfold nativeOrderKey
    rw [← hab _ _ hb, ← hab _ _ hb']
    exact h
  · rw [List.pairwise_flatMap]
    constructor
    · intro i _
      apply List.Pairwise.map _ _ (List.sortedLT_finRange n).pairwise
      intro a b hab
      exact Or.inr ⟨rfl, hab⟩
    · apply List.Pairwise.imp _ (List.sortedLT_finRange L.length).pairwise
      intro i j hij a ha b hb
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hb
      exact Or.inl hij

/-- Every active paper location appears in reverse order of layer and original gate index. -/
def paperOrder (L : PaperLayers (n := n) (q := q)) : List (PaperLocation L) :=
  (fullOrder (normalizedLayers L)).map (locationEquiv L).symm

theorem paperOrder_complete (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :
    i ∈ paperOrder L :=
  List.mem_map.mpr ⟨locationEquiv L i, mem_fullOrder _ _, Equiv.symm_apply_apply _ _⟩

theorem paperOrder_nodup (L : PaperLayers (n := n) (q := q)) : (paperOrder L).Nodup :=
  (fullOrder_nodup _).map (locationEquiv L).symm.injective

theorem paperOrder_descending (L : PaperLayers (n := n) (q := q)) :
    (paperOrder L).Pairwise (fun a b => earlier (paperOrderKey L b) (paperOrderKey L a)) := by
  apply List.Pairwise.map _ _ (fullOrder_descending (normalizedLayers L))
  intro a b h
  apply (locationEquiv_earlier L _ _).mp
  simpa only [Equiv.apply_symm_apply] using h

def paperOutputFault (L : PaperLayers (n := n) (q := q))
    (x : History (PaperLabel L)) (i : PaperLocation L) : Operator (QubitBasis n) :=
  (x i).elim 1 (fun a => propagate (paperSequenceEval (L.drop (i.1.val + 1))) (paperPhysicalFault L i a))

theorem paperOutputFault_eq_native (L : PaperLayers (n := n) (q := q))
    (x : History (PaperLabel L)) (i : PaperLocation L) :
    paperOutputFault L x i =
      FaultHistoryGeometry.outputFault (insertion (normalizedLayers L)) physicalFault
        (historyEquiv L x) (locationEquiv L i) := by
  unfold paperOutputFault FaultHistoryGeometry.outputFault
  rw [historyEquiv_apply]
  cases h : x i with
  | none => rfl
  | some a =>
    change propagate (paperSequenceEval (L.drop (i.1.val + 1))) (paperPhysicalFault L i a) =
      propagate (layerSequenceEval ((normalizedLayers L).drop ((locationEquiv L i).val.1.val + 1)))
        (physicalFault (locationEquiv L i) (labelEquiv L i a))
    rw [labelEquiv_physicalFault, locationEquiv_layer_index]
    simpa only [normalizedLayers, List.map_drop] using
      sequence_normalization_conjugation (L.drop (i.1.val + 1)) (paperPhysicalFault L i a)

/-- Output-frame error in the original order, using only faulty locations. -/
def paperOutputHistory (L : PaperLayers (n := n) (q := q)) (x : History (PaperLabel L)) :
    Operator (QubitBasis n) :=
  (((paperOrder L).filter fun i => decide (i ∈ faults x)).map (paperOutputFault L x)).prod

theorem paperOutputHistory_eq_native (L : PaperLayers (n := n) (q := q))
    (x : History (PaperLabel L)) :
    paperOutputHistory L x =
      FaultHistoryGeometry.outputHistory (insertion (normalizedLayers L)) physicalFault
        (historyEquiv L x) (chronologicalFaults (historyEquiv L x)) := by
  classical
  unfold paperOutputHistory paperOrder chronologicalFaults FaultHistoryGeometry.outputHistory
  rw [List.filter_map, List.map_map]
  have hf (i : Location (normalizedLayers L)) :
      decide ((locationEquiv L).symm i ∈ faults x) =
        decide (i ∈ faults (historyEquiv L x)) := by
    obtain ⟨j, rfl⟩ := (locationEquiv L).surjective i
    simp only [Equiv.symm_apply_apply, faults, Finset.mem_filter, Finset.mem_univ, true_and,
      historyEquiv_apply]
    cases x j <;> rfl
  change ((fullOrder (normalizedLayers L)).filter (fun i => decide ((locationEquiv L).symm i ∈ faults x)) |>.map _).prod = _
  simp only [hf]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  dsimp only [Function.comp_apply]
  rw [paperOutputFault_eq_native, Equiv.apply_symm_apply]

/-- The full noisy physical channel, including the ideal gate list, agrees
with the normalized native channel for corresponding independent laws. -/
theorem paper_noisyChannel_eq_native (L : PaperLayers (n := n) (q := q))
    (μ : Law (fun i : Location (normalizedLayers L) => FaultLabel i))
    (p : ℝ) (X : Operator (QubitBasis n)) :
    (∑ x, mass (pullLaw L μ) p x •
      propagate (paperOutputHistory L x * paperSequenceEval L) X) =
    ∑ y, mass μ p y • propagate
      (FaultHistoryGeometry.outputHistory (insertion (normalizedLayers L)) physicalFault y
        (chronologicalFaults y) * layerSequenceEval (normalizedLayers L)) X := by
  classical
  have hbranch (x : History (PaperLabel L)) :
      propagate (paperOutputHistory L x * paperSequenceEval L) X =
      propagate (FaultHistoryGeometry.outputHistory (insertion (normalizedLayers L)) physicalFault
        (historyEquiv L x) (chronologicalFaults (historyEquiv L x)) *
          layerSequenceEval (normalizedLayers L)) X := by
    rw [paperOutputHistory_eq_native]
    exact projectivelyEquivalent_conjugation_eq
      (projective_mul (projectivelyEquivalent_refl _) (sequence_normalization_phase L)) X
  simp_rw [hbranch, ← historyEquiv_mass]
  exact (historyEquiv L).sum_comp (fun y => mass μ p y • propagate
    (FaultHistoryGeometry.outputHistory (insertion (normalizedLayers L)) physicalFault y
      (chronologicalFaults y) * layerSequenceEval (normalizedLayers L)) X)

private def pushWeightEquiv (L : PaperLayers (n := n) (q := q)) (i : PaperLocation L) :
    (PaperLabel L i → ℝ) ≃ (FaultLabel (locationEquiv L i) → ℝ) :=
  (labelEquiv L i).arrowCongr (Equiv.refl ℝ)

private def pushWeights (L : PaperLayers (n := n) (q := q)) :
    (∀ i, PaperLabel L i → ℝ) ≃ (∀ j : Location (normalizedLayers L), FaultLabel j → ℝ) :=
  (locationEquiv L).piCongr (pushWeightEquiv L)

private theorem pushWeights_apply (L : PaperLayers (n := n) (q := q))
    (w : ∀ i, PaperLabel L i → ℝ) (i : PaperLocation L) (a : FaultLabel (locationEquiv L i)) :
    pushWeights L w (locationEquiv L i) a = w i ((labelEquiv L i).symm a) := by
  unfold pushWeights
  rw [Equiv.piCongr_apply_apply]
  rfl

def pushLaw (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) :
    Law (fun i : Location (normalizedLayers L) => FaultLabel i) where
  weight := pushWeights L μ.weight
  positive j a := by
    obtain ⟨i, rfl⟩ := (locationEquiv L).surjective j
    rw [pushWeights_apply]
    exact μ.positive _ _
  normalized j := by
    obtain ⟨i, rfl⟩ := (locationEquiv L).surjective j
    simp only [pushWeights_apply]
    exact ((labelEquiv L i).symm.sum_comp (μ.weight i)).trans (μ.normalized i)

private theorem law_ext {L : PaperLayers (n := n) (q := q)} {μ ν : Law (PaperLabel L)}
    (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem pull_push_history_law (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) :
    pullLaw L (pushLaw L μ) = μ := by
  have hw : (pullLaw L (pushLaw L μ)).weight = μ.weight := by
    funext i a
    change pushWeights L μ.weight (locationEquiv L i) (labelEquiv L i a) = μ.weight i a
    rw [pushWeights_apply, Equiv.symm_apply_apply]
  exact law_ext hw

theorem paper_noisyChannel_eq_normalize
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) (p : ℝ)
    (X : Operator (QubitBasis n)) :
    (∑ x, mass μ p x • propagate (paperOutputHistory L x * paperSequenceEval L) X) =
      ∑ y, mass (pushLaw L μ) p y • propagate
        (FaultHistoryGeometry.outputHistory (insertion (normalizedLayers L)) physicalFault y
          (chronologicalFaults y) * layerSequenceEval (normalizedLayers L)) X := by
  simpa only [pull_push_history_law] using paper_noisyChannel_eq_native L (pushLaw L μ) p X

#print axioms paper_noisyChannel_eq_normalize
#print axioms pull_push_history_law
#print axioms layerLocationEquiv_lt_iff
#print axioms paperOrder_complete
#print axioms paperOrder_nodup
#print axioms paperOrder_descending
#print axioms paperOutputHistory_eq_native
#print axioms paper_noisyChannel_eq_native

#print axioms layerLocationEquiv_support
#print axioms empty_support_no_fault
#print axioms sequence_normalization_conjugation
#print axioms locationEquiv_support
#print axioms labelEquiv_physicalFault
#print axioms historyEquiv_fault_count
#print axioms historyEquiv_mass
#print axioms normalization_probability_sum

end
end CriticalDepth.FaultHistoryNormalization
