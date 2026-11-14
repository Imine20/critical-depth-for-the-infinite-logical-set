import FaultNativeCeiling

/-!
The sharper lower exponent for circuits whose total unitary preserves
every tensor support under conjugation. The CSS rigidity proof would
supply this hypothesis simultaneously for all circuits in its depth range.
-/

namespace CriticalDepth.FaultSupportPreserving

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultDepthArithmetic
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.FaultNativeModel
open scoped Kronecker ENat

noncomputable section

variable {n q K : ℕ} {L : Layers n q}

/-- For example, a product of on-site unitaries has this property. -/
def PreservesSupports (U : Operator (QubitBasis n)) : Prop :=
  ∀ (O : Operator (QubitBasis n)) (S : Finset (Fin n)),
    SupportedOn O S → SupportedOn (propagate U O) S

private theorem propagate_cancel (U O : Operator (QubitBasis n)) (hU : IsUnitary U) :
    propagate U (propagate U.conjTranspose O) = O := by
  have h : U * U.conjTranspose = 1 := hU.2
  calc
    _ = (U * U.conjTranspose) * O * (U * U.conjTranspose) := by
      simp only [propagate, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = O := by rw [h, Matrix.one_mul, Matrix.mul_one]

private theorem outputFault_short (hq : 1 ≤ q)
    (hpreserve : PreservesSupports (layerSequenceEval L))
    (x : History (fun i : Location L => FaultLabel i)) (i : Location L) :
    ∃ S : Finset (Fin n),
      SupportedOn (outputFault (insertion L) physicalFault x i) S ∧
        S.card ≤ q ^ ceilHalf L.length := by
  cases hx : x i with
  | none =>
    refine ⟨∅, ?_, by simp⟩
    simpa only [outputFault, hx, Option.elim_none] using
      (supportedOn_one (dim := fun _ : Fin n => 2) ∅)
  | some p =>
    let a := insertion L i
    let U := layerSequenceEval L
    let O := propagate (layerSequenceEval a.after) (physicalFault i p)
    have hloc := physicalFault_supported i p
    have hl := congrArg List.length a.split
    simp only [List.length_append, List.length_cons] at hl
    have heq : outputFault (insertion L) physicalFault x i = O := by
      simp only [outputFault, hx, Option.elim_some, O, a]
    rw [heq]
    by_cases h : a.after.length + 1 ≤ ceilHalf L.length
    · obtain ⟨hs, hc⟩ := outputInsertionCone a.layer a.after a.slot _ hloc hq
      exact ⟨_, hs, hc.trans (Nat.pow_le_pow_right (by omega) h)⟩
    · have hbefore : a.before.length + 1 ≤ ceilHalf L.length := by
        unfold ceilHalf at h ⊢
        omega
      have hback : propagate U.conjTranspose O =
          propagate (layerSequenceEval ((a.before ++ [a.layer]).reverse.map Layer.adjoint))
            (physicalFault i p) := by
        unfold U O
        rw [show layerSequenceEval L = layerSequenceEval (a.before ++ a.layer :: a.after) from
          congrArg layerSequenceEval a.split]
        exact pullbackOutputInsertion a.before a.after a.layer _
      obtain ⟨hs, hc⟩ := inputInsertionCone a.before a.layer a.slot _ hloc hq
      have hs' := hpreserve (propagate U.conjTranspose O) _ (hback ▸ hs)
      rw [propagate_cancel _ _ (layerSequenceEval_isUnitary L)] at hs'
      exact ⟨_, hs', hc.trans (Nat.pow_le_pow_right (by omega) hbefore)⟩

private theorem shortHistory (hq : 1 ≤ q)
    (hpreserve : PreservesSupports (layerSequenceEval L))
    (x : History (fun i : Location L => FaultLabel i)) :
    ∃ S : Finset (Fin n),
      SupportedOn (outputHistory (insertion L) physicalFault x (chronologicalFaults x)) S ∧
      S.card ≤ (faults x).card * q ^ ceilHalf L.length := by
  classical
  choose S hs hcard using outputFault_short hq hpreserve x
  refine ⟨(faults x).biUnion S, ?_, ?_⟩
  · exact productSupported _ _ S _ (fun i hi => mem_chronologicalFaults x i hi)
      (fun i _ => hs i)
  · apply Finset.card_biUnion_le.trans
    exact (Finset.sum_le_sum fun i _ => hcard i).trans_eq (by simp)

private theorem scalar_from_gauge (C : Code n (fun _ => 2) K 1)
    (O : Operator (QubitBasis n)) (hg : GaugeOnly C O) :
    ∃ z : ℂ, C.encoding.conjTranspose * O * C.encoding =
      z • (1 : Operator (Fin K × Fin 1)) := by
  obtain ⟨Z, hZ⟩ := hg
  refine ⟨Z 0 0, hZ.trans ?_⟩
  ext ⟨i, a⟩ ⟨j, b⟩
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : b = 0 := Subsingleton.elim _ _
  simp [Matrix.one_apply, Matrix.smul_apply, mul_comm]

theorem scalarCrossTerms_of_preservesSupports
    (C : Code n (fun _ => 2) K 1) (d h : ℕ) (hq : 1 ≤ q)
    (hdet : DetectsBelow C d) (hL : L.length ≤ h)
    (hpreserve : PreservesSupports (layerSequenceEval L)) :
    ∀ x y : History (fun i : Location L => FaultLabel i),
      (faults x).card < upperEnvelope q d h → (faults y).card < upperEnvelope q d h →
      ∃ z : ℂ, (encodedBranch C x).conjTranspose * encodedBranch C y =
        z • (1 : Operator (Fin K × Fin 1)) := by
  intro x y hx hy
  obtain ⟨S, hs, hxS⟩ := shortHistory hq hpreserve x
  obtain ⟨T, ht, hyT⟩ := shortHistory hq hpreserve y
  let r := max (faults x).card (faults y).card
  let B := q ^ ceilHalf h
  have hB : 0 < B := pow_pos (by omega) _
  have hr : r < upperEnvelope q d h := max_lt hx hy
  have hrd : r * (2 * B) < d := by
    apply lt_of_not_ge
    intro hle
    exact (not_le_of_gt hr) ((ceilDiv_le_iff _ _ _ (by omega)).mpr hle)
  have hpow : q ^ ceilHalf L.length ≤ B := by
    apply Nat.pow_le_pow_right (by omega)
    unfold ceilHalf
    omega
  have hS : S.card ≤ r * B := hxS.trans (Nat.mul_le_mul (le_max_left _ _) hpow)
  have hT : T.card ≤ r * B := hyT.trans (Nat.mul_le_mul (le_max_right _ _) hpow)
  have hunion : (S ∪ T).card < d := by
    apply (Finset.card_union_le S T).trans_lt
    rw [Nat.mul_left_comm, Nat.two_mul] at hrd
    omega
  have hcomp := scalar_from_gauge C _ (hdet _ hunion _ (hs.conjTranspose.mul ht))
  obtain ⟨z, hz⟩ := hcomp
  exact ⟨z, by simpa only [encodedBranch, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hz⟩

theorem circuit_upperEnvelope_le_exponent [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (d h : ℕ) (hq : 1 ≤ q)
    (hdet : DetectsBelow C d) (hL : L.length ≤ h)
    (hpreserve : PreservesSupports (layerSequenceEval L))
    (μ : Law (fun i : Location L => FaultLabel i)) :
    (upperEnvelope q d h : ℕ∞) ≤ FaultExponent.exponent (circuitInfidelity C L μ) :=
  guaranteed_exponent_of_scalarCrossTerms μ _ (encodedBranch_isometry C)
    (upperEnvelope q d h) (scalarCrossTerms_of_preservesSupports C d h hq hdet hL hpreserve)
/-- The theorem of upper saturation follows once each allowed exact
circuit's total unitary has support-preserving conjugation. -/
theorem perCodeExponent_eq_upper_of_preservesSupports {k d h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstab : IsStabilizer C)
    (hdist : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h)
    (hrigidity : ∀ e : Experiment C q h, PreservesSupports (layerSequenceEval e.layers)) :
    perCodeExponent C q h = (upperEnvelope q d h : ℕ∞) := by
  apply le_antisymm
  · exact FaultNativeCeiling.perCodeExponent_ceiling C hstab hdist hd hq hh
  · apply le_iInf
    intro e
    exact circuit_upperEnvelope_le_exponent C d h (by omega) hdist.1 e.depth (hrigidity e) e.law

#print axioms circuit_upperEnvelope_le_exponent
#print axioms perCodeExponent_eq_upper_of_preservesSupports

end
end CriticalDepth.FaultSupportPreserving
