import MidpointEvenPauliCircuit
import MidpointNativeHistories

/-! The universal ceiling witnessed by the actual compression circuit of Theorem 3. -/

namespace CriticalDepth.MidpointFaultWitness

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultNativeModel
open CriticalDepth.IndependentFaultHistories CriticalDepth.FaultDepthArithmetic
open scoped Kronecker ENat
noncomputable section

variable {n q : ℕ}

theorem midpointLayer_activePauliSlots (p : Fin n → SinglePauli) (hq : 1 ≤ q)
    (M : Layer n (fun _ => 2) q) (hM : M.support = (midpointLayer p q hq).support) :
    activePauliSlots M p = activeSlots p q := by
  classical
  let S := pauliSupport p
  let e := S.equivFin.symm
  have hq₀ : 0 < q := by omega
  ext i
  change (i ∈ Finset.univ.filter fun j => ∃ x ∈ M.support j, p x ≠ .I) ↔
    i ∈ Finset.univ.filter fun j : Fin n => j.val < ceilDiv S.card q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hSupp : M.support i = paddedBucket S e q i :=
    congrFun hM i
  rw [hSupp]
  by_cases hi : i.val < ceilDiv S.card q
  · let b : Fin (ceilDiv S.card q) := ⟨i.val, hi⟩
    let x := bucketPivot S e q hq₀ b
    have hx := bucketPivot_mem S e q hq₀ b
    have hx₀ : p x ≠ .I := (Finset.mem_filter.mp (rankBucket_subset S e q b.val hx)).2
    have hMem : x ∈ paddedBucket S e q i := by
      simpa only [paddedBucket, hi, if_true] using hx
    exact iff_of_true ⟨x, hMem, hx₀⟩ hi
  · simp [paddedBucket, hi]

theorem compressedBucket_activePauliSlots (p : Fin n → SinglePauli) (hq : 1 ≤ q)
    (M : Layer n (fun _ => 2) q) (hM : M.support = (midpointLayer p q hq).support) :
    activePauliSlots M (bucketTarget (pauliSupport p) (pauliSupport p).equivFin.symm q
      (show 0 < q by omega)) = activeSlots p q := by
  classical
  let S := pauliSupport p
  let e := S.equivFin.symm
  have hq₀ : 0 < q := by omega
  let p' := bucketTarget S e q hq₀
  change activePauliSlots M p' = activeSlots p q
  ext i
  change (i ∈ Finset.univ.filter fun j => ∃ x ∈ M.support j, p' x ≠ .I) ↔
    i ∈ Finset.univ.filter fun j : Fin n => j.val < ceilDiv S.card q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hSupp : M.support i = paddedBucket S e q i := congrFun hM i
  rw [hSupp]
  by_cases hi : i.val < ceilDiv S.card q
  · let b : Fin (ceilDiv S.card q) := ⟨i.val, hi⟩
    let x := bucketPivot S e q hq₀ b
    have hx := bucketPivot_mem S e q hq₀ b
    have hx₀ : x ∈ bucketPivotSet S e q hq₀ :=
      Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
    have hMem : x ∈ paddedBucket S e q i := by
      simpa only [paddedBucket, hi, if_true] using hx
    refine iff_of_true ⟨x, hMem, ?_⟩ hi
    simp [p', bucketTarget, hx₀]
  · simp [paddedBucket, hi]

theorem exists_midpointPauliCircuit_exact_depth (p : Fin n → SinglePauli) (q h : ℕ)
    (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ (A B : Layers n q) (M : Layer n (fun _ => 2) q) (p' : Fin n → SinglePauli),
      let L := A ++ M :: B
      L.length = h ∧ A.length + 1 = ceilHalf h ∧ layerSequenceEval L = pauliMatrix 0 p ∧
      propagate (layerSequenceEval B) (pauliMatrix 0 p') = pauliMatrix 0 p ∧
      (∀ x ∈ pauliSupport p', ∃ i, x ∈ M.support i) ∧
      (activePauliSlots M p').card = ceilDiv (pauliSupport p).card (q ^ ceilHalf h) := by
  have hq₁ : 1 ≤ q := by omega
  have hq₀ : 0 < q := by omega
  let t := h / 2
  by_cases hE : h % 2 = 0
  · have ht : 1 ≤ t := by dsimp [t]; omega
    have hh' : h = 2 * t := by dsimp [t]; omega
    have hc : ceilHalf h = t := by unfold ceilHalf; omega
    obtain ⟨A, w, hA, heA, hw⟩ := pauli_compression_sequence q hq₁ p (t - 1)
    let S := pauliSupport w
    let e := S.equivFin.symm
    let p' := bucketTarget S e q hq₀
    obtain ⟨M₀, hs, hM⟩ := exists_lastCompressionLayer (q := q) w hq₁
    let M := absorbParallelPauli M₀ p'
    let C := A ++ [M₀]
    let B := C.reverse.map Layer.adjoint
    have hS : M.support = (midpointLayer w q hq₁).support := hs
    have hcov (i : Fin n) (hi : i ∈ pauliSupport p') : ∃ j, i ∈ M.support j := by
      rw [hS]
      exact paddedBucket_cover S e q hq₁ i (bucketTarget_support_subset S e q hq₀ hi)
    have hce : layerSequenceEval C = M₀.eval * layerSequenceEval A := by
      rw [layerSequenceEval_append, layerSequenceEval, layerSequenceEval, one_mul]
    have hc'' : layerSequenceEval C * pauliMatrix 0 p * star (layerSequenceEval C) =
        pauliMatrix 0 p' := by
      rw [hce, star_mul]
      calc
        _ = M₀.eval * (layerSequenceEval A * pauliMatrix 0 p *
            star (layerSequenceEval A)) * star M₀.eval := by simp only [mul_assoc]
        _ = _ := by rw [heA]; exact hM
    have hB : layerSequenceEval B = star (layerSequenceEval C) :=
      layerSequenceEval_reverse_adjoint C
    have hunit := (layerSequenceEval_isUnitary C).1
    have hProp : propagate (layerSequenceEval B) (pauliMatrix 0 p') = pauliMatrix 0 p := by
      rw [propagate, hB, ← Matrix.star_eq_conjTranspose, star_star, ← hc'']
      calc
        _ = (star (layerSequenceEval C) * layerSequenceEval C) * pauliMatrix 0 p *
            (star (layerSequenceEval C) * layerSequenceEval C) := by simp only [mul_assoc]
        _ = _ := by rw [hunit, one_mul, mul_one]
    refine ⟨A, B, M, p', ?_, ?_, ?_, hProp, hcov, ?_⟩
    · simp only [B, C, List.length_append, List.length_cons, List.length_map, List.length_reverse,
        List.length_nil, hA]
      omega
    · omega
    · rw [layerSequenceEval_append, layerSequenceEval]
      have hEval : M.eval = pauliMatrix 0 p' * M₀.eval :=
        absorbParallelPauli_eval M₀ p' hcov
      change (layerSequenceEval B * M.eval) * layerSequenceEval A = _
      rw [hEval]
      calc
        _ = layerSequenceEval B * pauliMatrix 0 p' * layerSequenceEval C := by
          rw [hce]
          simp only [mul_assoc]
        _ = _ := by
          rw [← hProp]
          congr 1
          rw [hB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    · rw [compressedBucket_activePauliSlots w hq₁ M hS, activeSlots_card w q hq₁,
        hw, compressedWeight_eq_ceilDiv_pow, ceilDiv_comp, ← pow_succ, hc]
      rw [show t - 1 + 1 = t by omega]
  · have hh' : h = 2 * t + 1 := by dsimp [t]; omega
    have hc : ceilHalf h = t + 1 := by unfold ceilHalf; omega
    obtain ⟨A, p', hA, hComp, hweight⟩ := pauli_compression_sequence q hq₁ p t
    let B := A.reverse.map Layer.adjoint
    let M := midpointPauliLayer p' hq₁
    have hE' : layerSequenceEval (A ++ M :: B) =
        propagate (layerSequenceEval B) (pauliMatrix 0 p') :=
      midpointPauliCircuit_eval A p' hq₁
    have hProp : propagate (layerSequenceEval B) (pauliMatrix 0 p') = pauliMatrix 0 p := by
      have hu := (layerSequenceEval_isUnitary A).1
      rw [propagate, show layerSequenceEval B = star (layerSequenceEval A) from
        layerSequenceEval_reverse_adjoint A, ← Matrix.star_eq_conjTranspose, star_star, ← hComp]
      calc
        _ = (star (layerSequenceEval A) * layerSequenceEval A) * pauliMatrix 0 p *
            (star (layerSequenceEval A) * layerSequenceEval A) := by simp only [mul_assoc]
        _ = _ := by rw [hu, one_mul, mul_one]
    refine ⟨A, B, M, p', ?_, by omega, hE'.trans hProp, hProp, ?_, ?_⟩
    · simp only [B, List.length_append, List.length_cons, List.length_map, List.length_reverse, hA]
      omega
    · exact paddedBucket_cover (pauliSupport p') (pauliSupport p').equivFin.symm q hq₁
    · rw [midpointLayer_activePauliSlots p' hq₁ M rfl, activeSlots_card p' q hq₁, hweight,
        compressedWeight_eq_ceilDiv_pow, ceilDiv_comp, ← pow_succ, hc]

theorem exists_logicalPauli_midpoint_histories {k d : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hS : IsStabilizer C) (hD : HasActualDistance C d)
    (q h : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ∃ e : Experiment C q h, e.layers.length = h ∧ e.logical.trace = 0 ∧
      ∃ x y : History (fun i : Location e.layers => FaultLabel i),
        x ≠ y ∧ (faults x).card = (ceilDiv d (q ^ ceilHalf h)) / 2 ∧
        (faults y).card = upperEnvelope q d h ∧
        (∀ i ∈ faults x ∪ faults y, i.val.1.val + 1 = ceilHalf h) ∧
        encodedBranch C y = encodedBranch C x * (e.logical ⊗ₖ (1 : Operator (Fin 1))) := by
  obtain ⟨p, W, hw, hENC, hAdj, hSq, hTr⟩ :=
    FaultStabilizerTrace.stabilizer_exact_traceless_logicalPauli C hS hD
  obtain ⟨A, B, M, p', hLength, hBalance, hEval, hProp, hcover, hCount⟩ :=
    exists_midpointPauliCircuit_exact_depth p q h hq hh
  let L := A ++ M :: B
  have hWu : IsUnitary W := by constructor <;> rw [hAdj, hSq]
  have hImp : Implements C (layerSequenceEval L) W := by
    refine ⟨hWu, 1, isUnitary_one, ?_⟩
    rw [hEval, hENC]
  let e : Experiment C q h := ⟨L, hLength.le, W, hImp, uniformLaw L⟩
  let w := ceilDiv d (q ^ ceilHalf h)
  have hw₀ : 0 < w := ceilDiv_pos (by omega) _
  have hLA : propagate (layerSequenceEval B) (pauliMatrix 0 p') * C.encoding =
      C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))) := by rw [hProp, hENC]
  have hCount' : (activePauliSlots M p').card = w := hCount.trans (congrArg (fun j => ceilDiv j _) hw)
  obtain ⟨x, y, hne, hx, hy, hWhere, hBranch⟩ :=
    exists_native_midpoint_histories C A B M p' W w hw₀ hcover hCount' hLA
  refine ⟨e, hLength, hTr, x, y, hne, hx, hy.trans (midpointHistoryCount q d h), ?_, hBranch⟩
  intro i hi
  rw [hWhere i hi]
  exact hBalance

#print axioms exists_midpointPauliCircuit_exact_depth
#print axioms exists_logicalPauli_midpoint_histories

end
end CriticalDepth.MidpointFaultWitness
