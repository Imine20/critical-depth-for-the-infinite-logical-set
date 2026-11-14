import FaultHistoryNormalization
import FaultNativeCeiling

/-!
# Terminal-recovery bounds for arbitrary paper gate lists

This module transports the output-frame normalized Bell loss from finite
paper gate lists to the bounded-slot native model.
-/

namespace CriticalDepth.FaultHistoryExperimentNormalization

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.Arithmetic
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultNativeModel
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.FaultDepthArithmetic
open scoped BigOperators ENat

variable {n q h K : ℕ}
variable [Nonempty (Fin K × Fin 1)]

def paperEncodedBranch (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (x : History (PaperLabel L)) :
    Matrix (QubitBasis n) (Fin K × Fin 1) ℂ :=
  paperOutputHistory L x * C.encoding

def paperCircuitInfidelity (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) : ℝ → ℝ :=
  optimalInfidelity μ (paperEncodedBranch C L)

theorem paperEncodedBranch_eq_native (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (x : History (PaperLabel L)) :
    paperEncodedBranch C L x = encodedBranch C (historyEquiv L x) := by
  simp only [paperEncodedBranch, encodedBranch, paperOutputHistory_eq_native]

theorem paperCircuitInfidelity_eq_native (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) :
    paperCircuitInfidelity C L μ = circuitInfidelity C (normalizedLayers L) (pushLaw L μ) := by
  funext p
  unfold paperCircuitInfidelity circuitInfidelity optimalInfidelity FaultExponent.optimalLoss
  congr 1
  apply congrArg Set.range
  funext R
  simp only [FaultExponent.lossAt, Manuscript20261114.expectedHistoryLoss,
    paperEncodedBranch_eq_native]
  simpa only [pull_push_history_law] using
    normalization_probability_sum L (pushLaw L μ) p
      (fun y => branchLoss (encodedBranch C y) R)

structure PaperExperiment (C : Code n (fun _ => 2) K 1) (q h : ℕ) where
  layers : PaperLayers (n := n) (q := q)
  depth : layers.length ≤ h
  logical : Operator (Fin K)
  exactAction : Implements C (paperSequenceEval layers) logical
  law : Law (PaperLabel layers)

def normalizeExperiment {C : Code n (fun _ => 2) K 1}
    (e : PaperExperiment C q h) : Experiment C q h where
  layers := normalizedLayers e.layers
  depth := by simpa only [normalizedLayers, List.length_map] using e.depth
  logical := e.logical
  exactAction := implements_of_projectivelyEquivalent_physical C
    (sequence_normalization_phase e.layers) e.exactAction
  law := pushLaw e.layers e.law

def paperPerCodeExponent (C : Code n (fun _ => 2) K 1) (q h : ℕ) : ℕ∞ :=
  FaultExponent.worstCaseExponent fun e : PaperExperiment C q h =>
    paperCircuitInfidelity C e.layers e.law

theorem native_perCodeExponent_le_paper (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    perCodeExponent C q h ≤ paperPerCodeExponent C q h := by
  apply le_iInf
  intro e
  change perCodeExponent C q h ≤ FaultExponent.exponent (paperCircuitInfidelity C e.layers e.law)
  rw [paperCircuitInfidelity_eq_native]
  exact iInf_le (fun t : Experiment C q h => FaultExponent.exponent
    (circuitInfidelity C t.layers t.law)) (normalizeExperiment e)

theorem paper_perCodeExponent_floor (C : Code n (fun _ => 2) K 1)
    (q d h : ℕ) (hq : 1 ≤ q) (hdetect : DetectsBelow C d) :
    (lowerEnvelope q d h : ℕ∞) ≤ paperPerCodeExponent C q h :=
  (perCodeExponent_floor C q d h hq hdetect).trans (native_perCodeExponent_le_paper C q h)

def paperLayersOfNative (L : Layers n q) : PaperLayers (n := n) (q := q) :=
  L.map Layer.toArbitrary

theorem paperLayersOfNative_eval (L : Layers n q) :
    paperSequenceEval (paperLayersOfNative L) = layerSequenceEval L := by
  simp only [paperLayersOfNative, paperSequenceEval, layerSequenceEval_eq_reverse_prod,
    List.map_map, Function.comp_def, Layer.toArbitrary_eval]

private def nativeLayerIndex (L : Layers n q) (i : Fin L.length) :
    Fin (paperLayersOfNative L).length :=
  ⟨i.val, by simpa only [paperLayersOfNative, List.length_map] using i.isLt⟩

private theorem get_paperLayersOfNative (L : Layers n q) (i : Fin L.length) :
    (paperLayersOfNative L).get (nativeLayerIndex L i) = (L.get i).toArbitrary := by
  simp only [paperLayersOfNative, nativeLayerIndex, List.get_eq_getElem, List.getElem_map]

private def nativeToPaperLocation (L : Layers n q) (i : Location L) :
    PaperLocation (paperLayersOfNative L) := by
  refine ⟨nativeLayerIndex L i.val.1, ⟨⟨i.val.2.val, ?_⟩, ?_⟩⟩
  · simpa only [get_paperLayersOfNative, Layer.toArbitrary, List.length_ofFn] using i.val.2.isLt
  · simp only [List.get_eq_getElem, paperLayersOfNative, nativeLayerIndex, List.getElem_map,
      Layer.toArbitrary, List.getElem_ofFn]
    exact i.property

private theorem nativeToPaperLocation_bijective (L : Layers n q) :
    Function.Bijective (nativeToPaperLocation L) := by
  constructor
  · intro i j hij
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z : PaperLocation (paperLayersOfNative L) => z.1.val) hij)
    · exact Fin.ext (congrArg (fun z : PaperLocation (paperLayersOfNative L) => z.2.val.val) hij)
  · rintro ⟨j, a⟩
    let i : Fin L.length :=
      ⟨j.val, by simpa only [paperLayersOfNative, List.length_map] using j.isLt⟩
    have hj : nativeLayerIndex L i = j := Fin.ext rfl
    have hget : (paperLayersOfNative L).get j = (L.get i).toArbitrary :=
      (congrArg (paperLayersOfNative L).get hj).symm.trans (get_paperLayersOfNative L i)
    have ha : a.val.val < n := by
      simpa only [hget, Layer.toArbitrary, List.length_ofFn] using a.val.isLt
    let k : Fin n := ⟨a.val.val, ha⟩
    have hlocal (l : PaperLayer (n := n) (q := q)) (hl : l = (L.get i).toArbitrary)
        (b : Fin l.gates.length) (hb : b.val < n)
        (hn : (l.gates.get b).support.Nonempty) :
        ((L.get i).support ⟨b.val, hb⟩).Nonempty := by
      subst l
      rw [List.get_eq_getElem] at hn
      simp only [Layer.toArbitrary] at hn
      rw [List.getElem_ofFn] at hn
      exact hn
    have hab : (supportAt L (i, k)).Nonempty :=
      hlocal _ hget a.val ha a.property
    refine ⟨⟨(i, k), hab⟩, ?_⟩
    have paperLocation_ext (u v : PaperLocation (paperLayersOfNative L))
        (huv : u.1.val = v.1.val) (hslot : u.2.val.val = v.2.val.val) : u = v := by
      rcases u with ⟨u, a⟩
      rcases v with ⟨v, b⟩
      have huv' : u = v := Fin.ext huv
      subst v
      have hab' : a = b := Subtype.ext (Fin.ext hslot)
      subst b
      rfl
    exact paperLocation_ext _ _ rfl rfl

private def reverseLocationEquiv (L : Layers n q) :
    Location L ≃ PaperLocation (paperLayersOfNative L) :=
  Equiv.ofBijective _ (nativeToPaperLocation_bijective L)

private theorem reverseLocationEquiv_support (L : Layers n q) (i : Location L) :
    paperSupport (paperLayersOfNative L) (reverseLocationEquiv L i) = supportAt L i.val := by
  change paperSupport (paperLayersOfNative L) (nativeToPaperLocation L i) = supportAt L i.val
  simp only [paperSupport, nativeToPaperLocation, paperLayersOfNative, nativeLayerIndex,
    List.get_eq_getElem, List.getElem_map, Layer.toArbitrary, List.getElem_ofFn, supportAt]

private def reverseLabelEquiv (L : Layers n q) (i : Location L) :
    FaultLabel i ≃ PaperLabel (paperLayersOfNative L) (reverseLocationEquiv L i) :=
  Equiv.cast (congrArg (fun S : Finset (Fin n) => {p : S → SinglePauli // p ≠ fun _ => .I})
    (reverseLocationEquiv_support L i).symm)

private theorem reverseLabelEquiv_physicalFault (L : Layers n q)
    (i : Location L) (a : FaultLabel i) :
    paperPhysicalFault (paperLayersOfNative L) (reverseLocationEquiv L i)
      (reverseLabelEquiv L i a) = physicalFault i a := by
  let f (S : Finset (Fin n)) (x : {p : S → SinglePauli // p ≠ fun _ => .I}) :=
    pauliMatrix 0 (extendLocalPauli S x.val)
  have h (S T : Finset (Fin n)) (hST : S = T)
      (x : {p : S → SinglePauli // p ≠ fun _ => .I}) :
      f T (Equiv.cast (congrArg (fun R : Finset (Fin n) =>
        {p : R → SinglePauli // p ≠ fun _ => .I}) hST) x) = f S x := by subst T; rfl
  exact h _ _ (reverseLocationEquiv_support L i).symm a

def reverseHistoryEquiv (L : Layers n q) :
    History (fun i : Location L => FaultLabel i) ≃ History (PaperLabel (paperLayersOfNative L)) :=
  (reverseLocationEquiv L).piCongr (fun i => Equiv.optionCongr (reverseLabelEquiv L i))

private theorem reverseHistoryEquiv_apply (L : Layers n q)
    (x : History (fun i : Location L => FaultLabel i)) (i : Location L) :
    reverseHistoryEquiv L x (reverseLocationEquiv L i) = (x i).map (reverseLabelEquiv L i) :=
  Equiv.piCongr_apply_apply _ _ _ _

private theorem reverseOrder_eq (L : Layers n q) :
    (fullOrder L).map (reverseLocationEquiv L) = paperOrder (paperLayersOfNative L) := by
  let P := paperLayersOfNative L
  let T := (fullOrder L).map (reverseLocationEquiv L)
  have hT : T.Pairwise (fun a b => earlier (paperOrderKey P b) (paperOrderKey P a)) := by
    apply List.Pairwise.map _ _ (fullOrder_descending L)
    intro a b hab
    exact hab
  have hperm : T.Perm (paperOrder P) := by
    apply (List.perm_ext_iff_of_nodup ((fullOrder_nodup L).map (reverseLocationEquiv L).injective)
      (paperOrder_nodup P)).mpr
    intro j
    constructor
    · intro _
      exact paperOrder_complete P j
    · intro _
      obtain ⟨i, rfl⟩ := (reverseLocationEquiv L).surjective j
      exact List.mem_map.mpr ⟨i, mem_fullOrder L i, rfl⟩
  apply List.Perm.eq_of_pairwise _ hT (paperOrder_descending P) hperm
  intro a b _ _ hab hba
  exfalso
  unfold earlier at hab hba
  omega

private theorem reverseOutputFault_eq (L : Layers n q)
    (x : History (fun i : Location L => FaultLabel i)) (i : Location L) :
    paperOutputFault (paperLayersOfNative L) (reverseHistoryEquiv L x) (reverseLocationEquiv L i) =
      FaultHistoryGeometry.outputFault (insertion L) physicalFault x i := by
  unfold paperOutputFault FaultHistoryGeometry.outputFault
  rw [reverseHistoryEquiv_apply]
  cases h : x i with
  | none => rfl
  | some a =>
    change FaultCircuitSupport.propagate
      (paperSequenceEval ((paperLayersOfNative L).drop (i.val.1.val + 1)))
      (paperPhysicalFault (paperLayersOfNative L) (reverseLocationEquiv L i)
        (reverseLabelEquiv L i a)) =
      FaultCircuitSupport.propagate (layerSequenceEval (L.drop (i.val.1.val + 1))) (physicalFault i a)
    rw [reverseLabelEquiv_physicalFault]
    have he : (paperLayersOfNative L).drop (i.val.1.val + 1) =
        paperLayersOfNative (L.drop (i.val.1.val + 1)) := (List.map_drop).symm
    rw [he, paperLayersOfNative_eval]

private theorem reverseOutputHistory_eq (L : Layers n q)
    (x : History (fun i : Location L => FaultLabel i)) :
    paperOutputHistory (paperLayersOfNative L) (reverseHistoryEquiv L x) =
      FaultHistoryGeometry.outputHistory (insertion L) physicalFault x (chronologicalFaults x) := by
  classical
  unfold paperOutputHistory chronologicalFaults FaultHistoryGeometry.outputHistory
  rw [← reverseOrder_eq L, List.filter_map, List.map_map]
  have hf (i : Location L) :
      decide (reverseLocationEquiv L i ∈ faults (reverseHistoryEquiv L x)) =
        decide (i ∈ faults x) := by
    simp only [faults, Finset.mem_filter, Finset.mem_univ, true_and, reverseHistoryEquiv_apply]
    cases x i <;> rfl
  change ((fullOrder L).filter (fun i => decide (reverseLocationEquiv L i ∈ faults (reverseHistoryEquiv L x))) |>.map _).prod = _
  simp only [hf]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  exact reverseOutputFault_eq L x i

private def reverseWeightEquiv (L : Layers n q) (i : Location L) :
    (FaultLabel i → ℝ) ≃ (PaperLabel (paperLayersOfNative L) (reverseLocationEquiv L i) → ℝ) :=
  (reverseLabelEquiv L i).arrowCongr (Equiv.refl ℝ)

private def reverseWeights (L : Layers n q) :
    (∀ i : Location L, FaultLabel i → ℝ) ≃ (∀ j, PaperLabel (paperLayersOfNative L) j → ℝ) :=
  (reverseLocationEquiv L).piCongr (reverseWeightEquiv L)

private theorem reverseWeights_apply (L : Layers n q)
    (w : ∀ i : Location L, FaultLabel i → ℝ) (i : Location L)
    (a : PaperLabel (paperLayersOfNative L) (reverseLocationEquiv L i)) :
    reverseWeights L w (reverseLocationEquiv L i) a = w i ((reverseLabelEquiv L i).symm a) := by
  unfold reverseWeights
  rw [Equiv.piCongr_apply_apply]
  rfl

def reverseLaw (L : Layers n q)
    (μ : Law (fun i : Location L => FaultLabel i)) : Law (PaperLabel (paperLayersOfNative L)) where
  weight := reverseWeights L μ.weight
  positive j a := by
    obtain ⟨i, rfl⟩ := (reverseLocationEquiv L).surjective j
    rw [reverseWeights_apply]
    exact μ.positive _ _
  normalized j := by
    obtain ⟨i, rfl⟩ := (reverseLocationEquiv L).surjective j
    simp only [reverseWeights_apply]
    exact ((reverseLabelEquiv L i).symm.sum_comp (μ.weight i)).trans (μ.normalized i)

private theorem reverseLaw_apply (L : Layers n q)
    (μ : Law (fun i : Location L => FaultLabel i)) (i : Location L) (a : FaultLabel i) :
    (reverseLaw L μ).weight (reverseLocationEquiv L i) (reverseLabelEquiv L i a) =
      μ.weight i a := by
  change reverseWeights L μ.weight (reverseLocationEquiv L i) (reverseLabelEquiv L i a) = _
  rw [reverseWeights_apply, Equiv.symm_apply_apply]

theorem reverseHistoryEquiv_mass (L : Layers n q)
    (μ : Law (fun i : Location L => FaultLabel i)) (p : ℝ)
    (x : History (fun i : Location L => FaultLabel i)) :
    mass (reverseLaw L μ) p (reverseHistoryEquiv L x) = mass μ p x := by
  unfold mass
  rw [← (reverseLocationEquiv L).prod_comp
    (fun j => localMass (reverseLaw L μ) p j (reverseHistoryEquiv L x j))]
  apply Finset.prod_congr rfl
  intro i _
  rw [reverseHistoryEquiv_apply]
  cases h : x i with
  | none => rfl
  | some a =>
    change (reverseLaw L μ).weight (reverseLocationEquiv L i) (reverseLabelEquiv L i a) * p = _
    rw [reverseLaw_apply]
    rfl

theorem paperEncodedBranch_eq_reverse (C : Code n (fun _ => 2) K 1)
    (L : Layers n q) (x : History (fun i : Location L => FaultLabel i)) :
    paperEncodedBranch C (paperLayersOfNative L) (reverseHistoryEquiv L x) =
      encodedBranch C x := by
  simp only [paperEncodedBranch, reverseOutputHistory_eq, encodedBranch]

theorem nativeCircuitInfidelity_eq_paper (C : Code n (fun _ => 2) K 1)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i)) :
    circuitInfidelity C L μ = paperCircuitInfidelity C (paperLayersOfNative L) (reverseLaw L μ) := by
  funext p
  unfold paperCircuitInfidelity circuitInfidelity optimalInfidelity FaultExponent.optimalLoss
  congr 1
  apply congrArg Set.range
  funext R
  simp only [FaultExponent.lossAt, Manuscript20261114.expectedHistoryLoss]
  conv_rhs =>
    rw [← (reverseHistoryEquiv L).sum_comp (fun y =>
      mass (reverseLaw L μ) p y * branchLoss (paperEncodedBranch C (paperLayersOfNative L) y) R)]
  simp only [reverseHistoryEquiv_mass, paperEncodedBranch, reverseOutputHistory_eq, encodedBranch]

def paperExperimentOfNative {C : Code n (fun _ => 2) K 1}
    (e : Experiment C q h) : PaperExperiment C q h where
  layers := paperLayersOfNative e.layers
  depth := by simpa only [paperLayersOfNative, List.length_map] using e.depth
  logical := e.logical
  exactAction := by simpa only [paperLayersOfNative_eval] using e.exactAction
  law := reverseLaw e.layers e.law

theorem paperPerCodeExponent_eq_native (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    paperPerCodeExponent C q h = perCodeExponent C q h := by
  apply le_antisymm _ (native_perCodeExponent_le_paper C q h)
  apply le_iInf
  intro e
  change paperPerCodeExponent C q h ≤ FaultExponent.exponent (circuitInfidelity C e.layers e.law)
  rw [nativeCircuitInfidelity_eq_paper]
  exact iInf_le (fun t : PaperExperiment C q h => FaultExponent.exponent
    (paperCircuitInfidelity C t.layers t.law)) (paperExperimentOfNative e)

theorem stabilizer_paperPerCodeExponent_envelopes {k d : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstabilizer : IsStabilizer C)
    (hdistance : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    (lowerEnvelope q d h : ℕ∞) ≤ paperPerCodeExponent C q h ∧
      paperPerCodeExponent C q h ≤ (upperEnvelope q d h : ℕ∞) := by
  rw [paperPerCodeExponent_eq_native]
  exact FaultNativeCeiling.stabilizer_perCodeExponent_envelopes C hstabilizer hdistance hd hq hh

#print axioms stabilizer_paperPerCodeExponent_envelopes

#print axioms nativeCircuitInfidelity_eq_paper
#print axioms paperPerCodeExponent_eq_native

#print axioms paperEncodedBranch_eq_native
#print axioms paperCircuitInfidelity_eq_native
#print axioms native_perCodeExponent_le_paper
#print axioms paper_perCodeExponent_floor

end
end CriticalDepth.FaultHistoryExperimentNormalization
