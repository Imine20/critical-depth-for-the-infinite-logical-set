import MidpointPauliCircuit

/-!
At an even depth, the single-site Paulis are absorbed into the last
compression layer without adding a native location.
-/

namespace CriticalDepth.MidpointFaultWitness

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultNativeModel
open scoped BigOperators

noncomputable section
variable {n q : ℕ}

theorem exists_lastCompressionLayer (p : Fin n → SinglePauli) (hq : 1 ≤ q) :
    let S := pauliSupport p
    let e := S.equivFin.symm
    let p' := bucketTarget S e q (show 0 < q by omega)
    ∃ L : Layer n (fun _ => 2) q,
      L.support = (midpointLayer p q hq).support ∧
      L.eval * pauliMatrix 0 p * star L.eval = pauliMatrix 0 p' := by
  classical
  intro S e p'
  let M := midpointLayer p q hq
  have hq₀ : 0 < q := by omega
  have hg (i : Fin n) : ∃ U : Operator (QubitBasis n),
      IsUnitary U ∧ SupportedOn U (M.support i) ∧
      U * pauliMatrix 0 (maskPauli p (M.support i)) * star U =
        pauliMatrix 0 (maskPauli p' (M.support i)) := by
    by_cases hi : i.val < ceilDiv S.card q
    · let b : Fin (ceilDiv S.card q) := ⟨i.val, hi⟩
      let j := bucketPivot S e q hq₀ b
      have hSupp : M.support i = rankBucket S e q i.val := by
        simp [M, midpointLayer, S, e, paddedBucket, hi]
      have hj : j ∈ M.support i := by
        rw [hSupp]
        exact bucketPivot_mem S e q hq₀ b
      have hj₀ : p j ≠ .I := (Finset.mem_filter.mp
        (rankBucket_subset S e q i.val (bucketPivot_mem S e q hq₀ b))).2
      have hout (k : Fin n) (hk : k ∉ M.support i) : maskPauli p (M.support i) k = .I := by
        simp [maskPauli, hk]
      have hj₁ : maskPauli p (M.support i) j ≠ .I := by
        simpa [maskPauli, hj] using hj₀
      obtain ⟨U, hU, hs, hc⟩ := pauli_group_to_single_site (M.support i)
        (maskPauli p (M.support i)) hout j hj hj₁
      refine ⟨U, hU, hs, hc.trans ?_⟩
      rw [hSupp]
      exact congrArg (pauliMatrix 0) (mask_bucketTarget_eq_single S e q hq₀ b).symm
    · have he : M.support i = ∅ := by
        simp [M, midpointLayer, S, e, paddedBucket, hi]
      refine ⟨1, isUnitary_one, supportedOn_one _, ?_⟩
      simp [he, maskPauli_empty]
  choose gate hu hs hc using hg
  let L : Layer n (fun _ => 2) q := { M with gate := gate, locality := hs, unitary := hu }
  refine ⟨L, rfl, ?_⟩
  apply L.conjugate_pauli_of_masked_blocks p p'
  · exact paddedBucket_cover S e q hq
  · intro i hi
    exact paddedBucket_cover S e q hq i (bucketTarget_support_subset S e q hq₀ hi)
  · exact hc

def absorbParallelPauli (L : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli) :
    Layer n (fun _ => 2) q :=
  { L with
    gate := fun i => pauliMatrix 0 (maskPauli p (L.support i)) * L.gate i
    locality := fun i => by
      simpa only [Finset.union_self] using
        (maskPauli_supportedOn p (L.support i)).mul (L.locality i)
    unitary := fun i => isUnitary_mul (unphased_pauliMatrix_isUnitary _) (L.unitary i) }

theorem absorbParallelPauli_eval (L : Layer n (fun _ => 2) q) (p : Fin n → SinglePauli)
    (hcover : ∀ i ∈ pauliSupport p, ∃ j, i ∈ L.support j) :
    (absorbParallelPauli L p).eval = pauliMatrix 0 p * L.eval := by
  classical
  let P := fun i => pauliMatrix 0 (maskPauli p (L.support i))
  have hp : (List.ofFn P).Pairwise Commute := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact (maskPauli_supportedOn p _).commute (maskPauli_supportedOn p _)
      (L.disjoint _ _ (fun he => (Nat.ne_of_lt hij) (congrArg Fin.val he)))
  have hprod : (List.ofFn P).reverse.prod = pauliMatrix 0 p :=
    (((List.reverse_perm (List.ofFn P)).symm).prod_eq' hp).symm.trans
      (pauliMatrix_eq_masked_product p L.support L.disjoint hcover).symm
  change (List.ofFn fun i => P i * L.gate i).reverse.prod = _
  rw [layerEval_withPostGateFaults L P (fun i => maskPauli_supportedOn p (L.support i)), hprod]

theorem exists_even_midpointPauliCircuit (p : Fin n → SinglePauli) (q t : ℕ)
    (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ (A : Layers n q) (L : Layer n (fun _ => 2) q) (p' : Fin n → SinglePauli),
      let B := A ++ [L]
      let C := A ++ [absorbParallelPauli L p'] ++ B.reverse.map Layer.adjoint
      C.length = 2 * t ∧ layerSequenceEval C = pauliMatrix 0 p ∧
      (pauliSupport p').card = ceilDiv (pauliSupport p).card (q ^ t) ∧
      (∀ i ∈ pauliSupport p', ∃ j, i ∈ L.support j) := by
  have hq₀ : 0 < q := by omega
  have hq₁ : 1 ≤ q := by omega
  obtain ⟨A, w, hA, heA, hw⟩ := pauli_compression_sequence q hq₁ p (t - 1)
  let S := pauliSupport w
  let e := S.equivFin.symm
  let p' := bucketTarget S e q hq₀
  obtain ⟨L, hSupport, hL⟩ := exists_lastCompressionLayer (q := q) w hq₁
  have hcover (i : Fin n) (hi : i ∈ pauliSupport p') : ∃ j, i ∈ L.support j := by
    rw [hSupport]
    exact paddedBucket_cover S e q hq₁ i (bucketTarget_support_subset S e q hq₀ hi)
  refine ⟨A, L, p', ?_, ?_, ?_, hcover⟩
  · simp only [List.length_append, List.length_singleton, List.length_map, List.length_reverse, hA]
    omega
  · let C := A ++ [L]
    let D := A ++ [absorbParallelPauli L p']
    change layerSequenceEval (D ++ C.reverse.map Layer.adjoint) = pauliMatrix 0 p
    have hD : layerSequenceEval D = (pauliMatrix 0 p' * L.eval) * layerSequenceEval A := by
      dsimp only [D]
      rw [layerSequenceEval_append]
      change (1 * (absorbParallelPauli L p').eval) * layerSequenceEval A = _
      rw [one_mul, absorbParallelPauli_eval L p' hcover]
    rw [layerSequenceEval_append, layerSequenceEval_reverse_adjoint, hD]
    have hc : layerSequenceEval (A ++ [L]) * pauliMatrix 0 p *
        star (layerSequenceEval (A ++ [L])) = pauliMatrix 0 p' := by
      rw [layerSequenceEval_append, layerSequenceEval, layerSequenceEval, one_mul, star_mul]
      calc
        _ = L.eval * (layerSequenceEval A * pauliMatrix 0 p *
              star (layerSequenceEval A)) * star L.eval := by simp only [mul_assoc]
        _ = _ := by rw [heA, hL]
    have hstar : star (layerSequenceEval (A ++ [L])) * layerSequenceEval (A ++ [L]) = 1 :=
      (layerSequenceEval_isUnitary _).1
    have hB : layerSequenceEval (A ++ [L]) = L.eval * layerSequenceEval A := by
      rw [layerSequenceEval_append, layerSequenceEval, layerSequenceEval, one_mul]
    calc
      _ = star (layerSequenceEval (A ++ [L])) * pauliMatrix 0 p' *
          layerSequenceEval (A ++ [L]) := by rw [hB]; simp only [mul_assoc]
      _ = pauliMatrix 0 p := by
        rw [← hc]
        calc
          _ = (star (layerSequenceEval (A ++ [L])) * layerSequenceEval (A ++ [L])) *
              pauliMatrix 0 p *
              (star (layerSequenceEval (A ++ [L])) * layerSequenceEval (A ++ [L])) := by
            simp only [mul_assoc]
          _ = _ := by rw [hstar, one_mul, mul_one]
  · rw [bucketTarget_support_card, hw, compressedWeight_eq_ceilDiv_pow, ceilDiv_comp, ← pow_succ]
    rw [show t - 1 + 1 = t by omega]

#print axioms exists_even_midpointPauliCircuit

end
end CriticalDepth.MidpointFaultWitness
