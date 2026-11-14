import FaultDepthArithmetic

/-!
# Matrix support of propagated fault insertions

An insertion is specified by a split of the ideal circuit at its faulty
layer, a gate slot, and an operator supported on that gate. The proofs use
the repository's exact matrix evaluation and tensor support. The paired
history lemma is the distance-detection step of the Knill–Laflamme argument.
It does not construct a recovery channel.
-/

namespace CriticalDepth.FaultCircuitSupport

noncomputable section

open CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic
open scoped BigOperators Kronecker

variable {n q K g : ℕ} {dim : Fin n → ℕ}

abbrev PhysicalOperator (n : ℕ) (dim : Fin n → ℕ) :=
  Operator (PhysicalBasis n dim)

def propagate (U A : PhysicalOperator n dim) : PhysicalOperator n dim :=
  U * A * U.conjTranspose

private theorem adjoint_support (L : Layer n dim q) (i : Fin n) :
    L.adjoint.support i.rev = L.support i := by
  simp [Layer.adjoint, Fin.rev_rev]

/-- After the faulty layer, a supported fault only spreads through the
remaining layers. Its support starts with the arity of the faulty gate. -/
theorem outputInsertionCone (L : Layer n dim q) (after : List (Layer n dim q))
    (i : Fin n) (A : PhysicalOperator n dim) (hA : SupportedOn A (L.support i))
    (hq : 1 ≤ q) :
    SupportedOn (propagate (layerSequenceEval after) A)
      (layerSequenceCone after (L.support i)) ∧
    (layerSequenceCone after (L.support i)).card ≤ q ^ (after.length + 1) := by
  refine ⟨layerSequence_conjugate_supportedOn after (L.support i) hA, ?_⟩
  calc
    _ ≤ q ^ after.length * (L.support i).card :=
      layerSequenceCone_card_le after _ hq
    _ ≤ q ^ after.length * q := Nat.mul_le_mul_left _ (L.arity i)
    _ = _ := (pow_succ q after.length).symm

/-- In the input frame, conjugation back through the faulty layer keeps its
gate support unchanged. Only preceding layers can spread it. -/
theorem inputInsertionCone (before : List (Layer n dim q)) (L : Layer n dim q)
    (i : Fin n) (A : PhysicalOperator n dim) (hA : SupportedOn A (L.support i))
    (hq : 1 ≤ q) :
    SupportedOn
      (propagate (layerSequenceEval ((before ++ [L]).reverse.map Layer.adjoint)) A)
      (layerSequenceCone (before.reverse.map Layer.adjoint) (L.support i)) ∧
    (layerSequenceCone (before.reverse.map Layer.adjoint) (L.support i)).card ≤
      q ^ (before.length + 1) := by
  have hcone : L.adjoint.lightCone (L.support i) = L.support i := by
    rw [← adjoint_support L i, Layer.lightCone_support]
  have heq : (before ++ [L]).reverse.map Layer.adjoint =
      L.adjoint :: before.reverse.map Layer.adjoint := by simp
  refine ⟨?_, ?_⟩
  · have hs := layerSequence_conjugate_supportedOn
      ((before ++ [L]).reverse.map Layer.adjoint) (L.support i) hA
    rw [heq] at hs ⊢
    simpa only [propagate, layerSequenceCone, hcone] using hs
  · calc
      _ ≤ q ^ (before.reverse.map Layer.adjoint).length * (L.support i).card :=
        layerSequenceCone_card_le _ _ hq
      _ ≤ q ^ (before.reverse.map Layer.adjoint).length * q :=
        Nat.mul_le_mul_left _ (L.arity i)
      _ = _ := by simp only [List.length_map, List.length_reverse, pow_succ]

/-- Pulling the output-frame insertion through the ideal circuit cancels its
suffix and yields the input-frame insertion. -/
theorem pullbackOutputInsertion (before after : List (Layer n dim q))
    (L : Layer n dim q) (A : PhysicalOperator n dim) :
    propagate (layerSequenceEval (before ++ L :: after)).conjTranspose
        (propagate (layerSequenceEval after) A) =
      propagate (layerSequenceEval ((before ++ [L]).reverse.map Layer.adjoint)) A := by
  let B := layerSequenceEval (before ++ [L])
  let C := layerSequenceEval after
  have hC := (layerSequenceEval_isUnitary after).1
  change C.conjTranspose * C = 1 at hC
  have hfull : layerSequenceEval (before ++ L :: after) = C * B := by
    have hlist : before ++ L :: after = (before ++ [L]) ++ after := by
      simp [List.append_assoc]
    rw [hlist, layerSequenceEval_append]
  rw [hfull, layerSequenceEval_reverse_adjoint]
  change (C * B).conjTranspose * (C * A * C.conjTranspose) *
      ((C * B).conjTranspose).conjTranspose = B.conjTranspose * A * B.conjTranspose.conjTranspose
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc
    B.conjTranspose * (C.conjTranspose * (C * (A * (C.conjTranspose * (C * B))))) =
        B.conjTranspose * ((C.conjTranspose * C) * (A * ((C.conjTranspose * C) * B))) := by
      simp only [Matrix.mul_assoc]
    _ = B.conjTranspose * (A * B) := by simp [hC]

/-- After a native gate, its fault commutes with every other gate in that
layer because their supports are disjoint. This factors the interleaved
noisy layer into the fault product followed algebraically by the ideal
product, using the same multiplication order in both. -/
theorem interleavedLayer_eq_faultProduct (L : Layer n dim q)
    (fault : Fin n → PhysicalOperator n dim)
    (hfault : ∀ i, SupportedOn (fault i) (L.support i))
    (slots : List (Fin n)) (hslots : slots.Nodup) :
    (slots.map fun i => fault i * L.gate i).prod =
      (slots.map fault).prod * (slots.map L.gate).prod := by
  induction slots with
  | nil => simp
  | cons i slots ih =>
      have h := List.nodup_cons.mp hslots
      have hcomm : Commute (L.gate i) (slots.map fault).prod := by
        apply Commute.list_prod_right
        intro A hA
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hA
        have hij : i ≠ j := fun he => h.1 (he.symm ▸ hj)
        exact (L.locality i).commute (hfault j) (L.disjoint i j hij)
      simp only [List.map_cons, List.prod_cons, ih h.2]
      let F := (slots.map fault).prod
      let V := (slots.map L.gate).prod
      change (fault i * L.gate i) * (F * V) = (fault i * F) * (L.gate i * V)
      calc
        (fault i * L.gate i) * (F * V) = fault i * ((L.gate i * F) * V) := by
          simp only [Matrix.mul_assoc]
        _ = fault i * ((F * L.gate i) * V) := by rw [hcomm.eq]
        _ = (fault i * F) * (L.gate i * V) := by simp only [Matrix.mul_assoc]

theorem layerEval_withPostGateFaults (L : Layer n dim q)
    (fault : Fin n → PhysicalOperator n dim)
    (hfault : ∀ i, SupportedOn (fault i) (L.support i)) :
    (List.ofFn fun i => fault i * L.gate i).reverse.prod =
      (List.ofFn fault).reverse.prod * L.eval := by
  have hn : (List.finRange n).Nodup := by
    simpa only [List.ofFn_eq_map, List.map_id] using
      (List.nodup_ofFn_ofInjective Function.injective_id : (List.ofFn id : List (Fin n)).Nodup)
  simpa only [Layer.eval, List.ofFn_eq_map, List.map_reverse] using
    interleavedLayer_eq_faultProduct L fault hfault (List.finRange n).reverse (List.nodup_reverse.mpr hn)

/-- A noisy layer is specified by the product of its post-gate fault
operators on the left of its ideal evaluation. The list is in execution
order. -/
def noisyEval :
    List (Layer n dim q × PhysicalOperator n dim) → PhysicalOperator n dim
  | [] => 1
  | (L, F) :: steps => noisyEval steps * (F * L.eval)

/-- The list of suffix-conjugated layer faults in reverse execution order. -/
def propagatedFaults :
    List (Layer n dim q × PhysicalOperator n dim) → List (PhysicalOperator n dim)
  | [] => []
  | (_, F) :: steps =>
      propagatedFaults steps ++ [propagate (layerSequenceEval (steps.map Prod.fst)) F]

/-- Telescoping the noisy circuit produces the output-frame product. -/
theorem noisyEval_eq_propagatedFaults
    (steps : List (Layer n dim q × PhysicalOperator n dim)) :
    noisyEval steps =
      (propagatedFaults steps).prod * layerSequenceEval (steps.map Prod.fst) := by
  induction steps with
  | nil => simp [noisyEval, propagatedFaults, layerSequenceEval]
  | cons step steps ih =>
      rcases step with ⟨L, F⟩
      let U := layerSequenceEval (steps.map Prod.fst)
      let P := (propagatedFaults steps).prod
      have hU : U.conjTranspose * U = 1 :=
        (layerSequenceEval_isUnitary (steps.map Prod.fst)).1
      have hcancel : propagate U F * U = U * F := by
        simp only [propagate, Matrix.mul_assoc, hU, Matrix.mul_one]
      change noisyEval steps * (F * L.eval) =
        (propagatedFaults steps ++ [propagate U F]).prod * (U * L.eval)
      rw [ih, List.prod_append, List.prod_singleton]
      change (P * U) * (F * L.eval) = (P * propagate U F) * (U * L.eval)
      calc
        (P * U) * (F * L.eval) = (P * (U * F)) * L.eval := by
          simp only [Matrix.mul_assoc]
        _ = (P * (propagate U F * U)) * L.eval := by rw [hcancel]
        _ = (P * propagate U F) * (U * L.eval) := by simp only [Matrix.mul_assoc]

theorem residual_eq_propagatedFaults
    (steps : List (Layer n dim q × PhysicalOperator n dim)) :
    noisyEval steps * (layerSequenceEval (steps.map Prod.fst)).conjTranspose =
      (propagatedFaults steps).prod := by
  have hU : layerSequenceEval (steps.map Prod.fst) *
      (layerSequenceEval (steps.map Prod.fst)).conjTranspose = 1 :=
    (layerSequenceEval_isUnitary (steps.map Prod.fst)).2
  rw [noisyEval_eq_propagatedFaults, Matrix.mul_assoc, hU, Matrix.mul_one]

/-- Moving a product of output-frame faults to the input frame conjugates
each factor by the same ideal circuit. -/
theorem pullbackFaultProduct (U : PhysicalOperator n dim) (hU : IsUnitary U)
    (faults : List (PhysicalOperator n dim)) :
    propagate U.conjTranspose faults.prod =
      (faults.map (propagate U.conjTranspose)).prod := by
  have hleft : U.conjTranspose * U = 1 := hU.1
  have hright : U * U.conjTranspose = 1 := hU.2
  induction faults with
  | nil => simpa [propagate] using hleft
  | cons F faults ih =>
      simp only [List.prod_cons, List.map_cons, ← ih]
      simp only [propagate, Matrix.conjTranspose_conjTranspose]
      calc
        U.conjTranspose * (F * faults.prod) * U =
            U.conjTranspose * (F * ((U * U.conjTranspose) * faults.prod)) * U := by
          rw [hright, Matrix.one_mul]
        _ = (U.conjTranspose * F * U) * (U.conjTranspose * faults.prod * U) := by
          simp only [Matrix.mul_assoc]

/-- The product of the fault operators is supported on the union of their
supports, for any order of the specified locations. -/
theorem productSupported {ι : Type*} (locations : Finset ι)
    (order : List ι) (support : ι → Finset (Fin n))
    (fault : ι → PhysicalOperator n dim)
    (horder : ∀ i ∈ order, i ∈ locations)
    (hfault : ∀ i ∈ locations, SupportedOn (fault i) (support i)) :
    SupportedOn (order.map fault).prod (locations.biUnion support) := by
  apply supportedOn_list_prod
  intro A hA
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
  apply (hfault i (horder i hi)).mono
  intro site hsite
  exact Finset.mem_biUnion.mpr ⟨i, horder i hi, hsite⟩

/-- A pair of histories of at most `r < m₋(h)` faults has a jointly small
support in one of the two frames. Locations must be tagged by history.
The conjugation in the last hypothesis expresses that both products
describe the same cross term. -/
theorem pairedCrossTerm_detected {ι : Type*} (locations : Finset ι)
    (q d h r : ℕ) (layer : ι → ℕ) (inputSupport outputSupport : ι → Finset (Fin n))
    (inputTerm outputTerm U : PhysicalOperator n dim) (C : Code n dim K g)
    (hq : 1 ≤ q) (hcard : locations.card ≤ 2 * r) (hr : r < lowerEnvelope q d h)
    (hlayer : ∀ i ∈ locations, 1 ≤ layer i ∧ layer i ≤ h)
    (hinput : ∀ i ∈ locations, (inputSupport i).card ≤ q ^ layer i)
    (houtput : ∀ i ∈ locations, (outputSupport i).card ≤ q ^ (h - layer i + 1))
    (hinputTerm : SupportedOn inputTerm (locations.biUnion inputSupport))
    (houtputTerm : SupportedOn outputTerm (locations.biUnion outputSupport))
    (hframe : inputTerm = propagate U.conjTranspose outputTerm)
    (hdetect : DetectsBelow C d) (hU : IsUnitary U)
    (W : Operator (Fin K)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : U * C.encoding = C.encoding * (W ⊗ₖ Z))
    (hdual : C.encoding.conjTranspose * U = (W ⊗ₖ Z) * C.encoding.conjTranspose) :
    GaugeOnly C outputTerm := by
  rcases pairedHistories_oneFrame_lt locations q d h r layer
      (fun i => (inputSupport i).card) (fun i => (outputSupport i).card)
      hq hcard hr hlayer hinput houtput with hin | hout
  · have hsmall : (locations.biUnion inputSupport).card < d :=
      Finset.card_biUnion_le.trans_lt hin
    obtain ⟨N, hN⟩ := hdetect _ hsmall _ hinputTerm
    rw [hframe] at hN
    have hback :
        C.encoding.conjTranspose * U.conjTranspose * outputTerm * U * C.encoding =
          (1 : Operator (Fin K)) ⊗ₖ N := by
      simpa only [propagate, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hN
    refine ⟨Z * N * Z.conjTranspose, ?_⟩
    exact CriticalDepth.algebraic_gauge_frame_transfer C.encoding.conjTranspose C.encoding
      U U.conjTranspose outputTerm W W.conjTranspose Z Z.conjTranspose N
      hU.2 hU.1 hW.2 hW.1 hZ.2 hZ.1 hencoded hdual hback
  · exact hdetect _ (Finset.card_biUnion_le.trans_lt hout) _ houtputTerm

example (L : Layer n dim q) (i : Fin n) (A : PhysicalOperator n dim)
    (hA : SupportedOn A (L.support i)) (hq : 1 ≤ q) :
    (layerSequenceCone ([] : List (Layer n dim q)) (L.support i)).card ≤ q := by
  simpa using (outputInsertionCone L [] i A hA hq).2

#print axioms outputInsertionCone
#print axioms inputInsertionCone
#print axioms pullbackOutputInsertion
#print axioms interleavedLayer_eq_faultProduct
#print axioms layerEval_withPostGateFaults
#print axioms noisyEval_eq_propagatedFaults
#print axioms residual_eq_propagatedFaults
#print axioms pullbackFaultProduct
#print axioms productSupported
#print axioms pairedCrossTerm_detected

end

end CriticalDepth.FaultCircuitSupport
