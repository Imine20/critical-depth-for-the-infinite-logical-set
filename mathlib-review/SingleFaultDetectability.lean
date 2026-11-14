import MidpointExactFaultWitness

/-! The first depth at which a single native fault can be an undetectable logical Pauli. -/

namespace CriticalDepth.FaultNativeModel

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultDepthArithmetic
open CriticalDepth.IndependentFaultHistories CriticalDepth.MidpointFaultWitness
open scoped Kronecker

noncomputable section

/-- Below continuous onset, every individual supported insertion has scalar
compression in the output frame of an exact logical circuit. -/
theorem singleNativeFault_detectable_below_onset {n K q d h : ℕ}
    (C : Code n (fun _ => 2) K 1) (hD : DetectsBelow C d)
    (hq : 2 ≤ q) (hh : h < criticalDepth q d) (e : Experiment C q h)
    (i : Location e.layers) (p : FaultLabel i) :
    GaugeOnly C (propagate (layerSequenceEval (insertion e.layers i).after)
      (physicalFault i p)) := by
  let a := insertion e.layers i
  let U := layerSequenceEval e.layers
  let O := propagate (layerSequenceEval a.after) (physicalFault i p)
  change GaugeOnly C O
  have hq₁ : 1 ≤ q := by omega
  have hq₀ : 0 < q := by omega
  have hSplit := congrArg List.length a.split
  simp only [List.length_append, List.length_cons] at hSplit
  have hSmall : q ^ ceilHalf h < d := (below_threshold_iff q d h hq).mp hh
  have hLen := e.depth
  by_cases hAfter : a.after.length + 1 ≤ ceilHalf h
  · obtain ⟨hSupport, hCard⟩ := outputInsertionCone a.layer a.after a.slot _
      (physicalFault_supported i p) hq₁
    exact hD _ (hCard.trans_lt ((Nat.pow_le_pow_right hq₀ hAfter).trans_lt hSmall))
      _ hSupport
  · have hBefore : a.before.length + 1 ≤ ceilHalf h := by
      unfold ceilHalf at hAfter ⊢
      omega
    obtain ⟨hSupport, hCard⟩ := inputInsertionCone a.before a.layer a.slot _
      (physicalFault_supported i p) hq₁
    have hBack : propagate U.conjTranspose O =
        propagate (layerSequenceEval ((a.before ++ [a.layer]).reverse.map Layer.adjoint))
          (physicalFault i p) := by
      unfold U O
      rw [show layerSequenceEval e.layers = layerSequenceEval (a.before ++ a.layer :: a.after)
        from congrArg layerSequenceEval a.split]
      exact pullbackOutputInsertion a.before a.after a.layer _
    obtain ⟨T, hT⟩ := hD _ (hCard.trans_lt ((Nat.pow_le_pow_right hq₀ hBefore).trans_lt hSmall))
      _ hSupport
    rw [← hBack] at hT
    obtain ⟨hW, Z, hZ, hV⟩ := e.exactAction
    have hDual : C.encoding.conjTranspose * U =
        (e.logical ⊗ₖ Z) * C.encoding.conjTranspose := by
      change U * C.encoding = _ at hV
      simpa only [U, circuitOfLayers_eval] using
        (point_encoded_dual C (circuitOfLayers e.layers) e.logical Z hW hZ
          (by simpa only [U, circuitOfLayers_eval] using hV))
    have hU := layerSequenceEval_isUnitary e.layers
    have hInput : C.encoding.conjTranspose * U.conjTranspose * O * U * C.encoding =
        (1 : Operator (Fin K)) ⊗ₖ T := by
      simpa only [propagate, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hT
    exact ⟨Z * T * Z.conjTranspose,
      CriticalDepth.algebraic_gauge_frame_transfer C.encoding.conjTranspose C.encoding
        U U.conjTranspose O e.logical e.logical.conjTranspose Z Z.conjTranspose T
        hU.2 hU.1 hW.2 hW.1 hZ.2 hZ.1 hV hDual hInput⟩

/-- At the onset, one midpoint fault already acts as a traceless unitary
on the encoded subspace relative to the ideal action. -/
theorem exists_undetectable_singleNativeFault_at_onset {n k d q : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hS : IsStabilizer C)
    (hD : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) :
    let h := criticalDepth q d
    ∃ (e : Experiment C q h)
      (y : History (fun i : Location e.layers => FaultLabel i)),
      e.layers.length = h ∧ (faults y).card = 1 ∧ IsUnitary e.logical ∧
      e.logical.trace = 0 ∧
      encodedBranch C y = C.encoding * (e.logical ⊗ₖ (1 : Operator (Fin 1))) := by
  let h := criticalDepth q d
  have hh : 1 ≤ h := by
    have hLog := clog_pos_of_two_le q d hq hd
    unfold h criticalDepth
    omega
  have hq₀ : 0 < q := by omega
  have hPow : d ≤ q ^ ceilHalf h :=
    Nat.le_of_not_gt fun ht => (Nat.lt_irrefl h) ((below_threshold_iff q d h hq).mpr ht)
  have hBlocks : ceilDiv d (q ^ ceilHalf h) = 1 := by
    have hLe : ceilDiv d (q ^ ceilHalf h) ≤ 1 :=
      (ceilDiv_le_iff _ _ _ (pow_pos hq₀ _)).mpr (by simpa only [one_mul] using hPow)
    have hPos : 0 < ceilDiv d (q ^ ceilHalf h) := ceilDiv_pos (by omega) _
    omega
  obtain ⟨e, he, hTr, x, y, _, hx, hy, _, hBranch⟩ :=
    exists_logicalPauli_midpoint_histories C hS hD q h hd hq hh
  rw [hBlocks] at hx
  rw [← midpointHistoryCount, hBlocks] at hy
  have hxEmpty : faults x = ∅ := Finset.card_eq_zero.mp (by simpa using hx)
  have hOrder : chronologicalFaults x = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have hm := mem_chronologicalFaults x i hi
    rw [hxEmpty] at hm
    exact Finset.notMem_empty i hm
  refine ⟨e, y, he, ?_, e.exactAction.1, hTr, ?_⟩
  · exact hy.trans (by decide)
  · rw [hBranch]
    have hClean : encodedBranch C x = C.encoding := by
      rw [encodedBranch, hOrder]
      simp [outputHistory]
    rw [hClean]

#print axioms singleNativeFault_detectable_below_onset
#print axioms exists_undetectable_singleNativeFault_at_onset

end
end CriticalDepth.FaultNativeModel