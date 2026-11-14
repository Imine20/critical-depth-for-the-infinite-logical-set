import Q37PhysicalPhases
import Q37CanonicalLogicalPauli
import Q37HadamardFourier
import GenerationThresholds

/-!
# The Q37 native depth-one logical classes
-/

open scoped BigOperators Kronecker Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.FaultShorSaturation CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114.CliffordT
open CriticalDepth.Manuscript20261114.OneQubitEuler Matrix

noncomputable section

set_option maxHeartbeats 550000

private theorem blockOdd_eq_binary_dot (a : ℕ) (x : QubitBasis 37) :
    blockOdd (sitesOfNatMask 37 a) x =
      decide (dotProduct (wordOfNatMask 37 a) (binaryWordEquiv 37 x) = (1 : CSSBit)) := by
  unfold blockOdd
  have hsum :
      (∑ i ∈ sitesOfNatMask 37 a, binaryWordEquiv 37 x i) =
      dotProduct (wordOfNatMask 37 a) (binaryWordEquiv 37 x) := by
    rw [sitesOfNatMask, Finset.sum_filter]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    cases hi : a.testBit i.val <;> simp [wordOfNatMask, hi]
  rw [hsum]

private theorem filter_attach_length {α : Type*} (L : List α) (p : α → Bool) :
    (L.attach.filter (fun a => p a.val)).length = (L.filter p).length := by
  have hAttach : L.attach.map (fun a => id a.val) = L.map id := List.attach_map_val
  have hId : L.attach.map Subtype.val = L := by
    change L.attach.map (fun a => id a.val) = L
    simpa only [List.map_id] using hAttach
  have h : (L.attach.filter (p ∘ Subtype.val)).map Subtype.val = L.filter p := by
    rw [← List.filter_map]
    exact congrArg (List.filter p) hId
  change (L.attach.filter (p ∘ Subtype.val)).length = _
  simpa only [List.length_map] using congrArg List.length h

private theorem supports_count (L : List ℕ)
    (s : {a : ℕ // a ∈ L} → {S : Finset (Fin 37) // S.card ≤ 3})
    (hs : ∀ a, (s a).val = sitesOfNatMask 37 a.val)
    (x : QubitBasis 37) :
    countOddBlocks (L.attach.map s) x = oddWordCount L (binaryWordEquiv 37 x) := by
  let p (b : ℕ) := decide (dotProduct (wordOfNatMask 37 b) (binaryWordEquiv 37 x) = 1)
  have h : ((fun S => blockOdd S.val x) ∘ s) = fun a => p a.val := by
    funext a
    change blockOdd (s a).val x = p a.val
    rw [hs a]
    exact blockOdd_eq_binary_dot a.val x
  calc
    _ = (L.attach.filter (fun a => p a.val)).length := by
      unfold countOddBlocks
      rw [List.filter_map, List.length_map]
      exact congrArg (fun f => (L.attach.filter f).length) h
    _ = (L.filter p).length := filter_attach_length L p
    _ = _ := rfl

private theorem q37ParitySupport_count (x : QubitBasis 37) :
    countOddBlocks q37ParitySupports x = oddWordCount parityBlocks (binaryWordEquiv 37 x) :=
  supports_count parityBlocks paritySupport (fun _ => rfl) x

private theorem q37LineSupport_count (x : QubitBasis 37) :
    countOddBlocks q37LineSupports x = oddWordCount lineBlocks (binaryWordEquiv 37 x) :=
  supports_count lineBlocks lineSupport (fun _ => rfl) x


private theorem q37Parity_count_nonzero (x : QubitBasis 37) (b : Fin 2 × Fin 1)
    (h : q37CanonicalEncoding x b ≠ 0) :
    countOddBlocks q37ParitySupports x % 8 = if b.1 = 0 then 0 else 7 := by
  obtain ⟨v, hword⟩ := q37Canonical_nonzero_word x b h
  rw [q37ParitySupport_count, hword]
  by_cases hb : b.1 = 0
  · simpa [hb] using q37_parity_phase_on_span false v
  · simpa [hb] using q37_parity_phase_on_span true v

private theorem q37Line_count_nonzero (x : QubitBasis 37) (b : Fin 2 × Fin 1)
    (h : q37DualEncoding x b ≠ 0) :
    countOddBlocks q37LineSupports x % 4 = if b.1 = 0 then 0 else 3 := by
  obtain ⟨v, hword⟩ := q37Dual_nonzero_word x b h
  rw [q37LineSupport_count, hword]
  by_cases hb : b.1 = 0
  · simpa [hb] using q37_line_phase_on_span false v
  · simpa [hb] using q37_line_phase_on_span true v

private def zPhase (m : ℕ) : Circle := Circle.exp (2 * Real.pi / m)

private theorem zPhase_pow (m : ℕ) (hm : m ≠ 0) : (zPhase m : ℂ) ^ m = 1 := by
  rw [zPhase, ← Circle.coe_pow, ← Circle.exp_nsmul, nsmul_eq_mul,
    show (m : ℝ) * (2 * Real.pi / m) = 2 * Real.pi by
      field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm]]
  simp [Circle.exp_two_pi]

private theorem zPhase_pred (m : ℕ) (hm : 0 < m) :
    (zPhase m : ℂ) ^ (m - 1) = (zPhase m : ℂ)⁻¹ := by
  have hz : (zPhase m : ℂ) ≠ 0 := (zPhase m).coe_ne_zero
  apply (mul_eq_one_iff_eq_inv₀ hz).mp
  rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m), zPhase_pow m (by omega)]

private def negativePhaseDiagonal (m : ℕ) : QubitOperator :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else (zPhase m : ℂ)⁻¹)

private theorem gaugeOne_diag (m : ℕ) :
    negativePhaseDiagonal m ⊗ₖ (1 : Operator (Fin 1)) =
      Matrix.diagonal (fun i : Fin 2 × Fin 1 => if i.1 = 0 then 1 else (zPhase m : ℂ)⁻¹) := by
  ext i j
  have h₂ : i.2 = j.2 := Subsingleton.elim _ _
  have h₁ : i = j ↔ i.1 = j.1 := ⟨fun h => congrArg Prod.fst h, fun h => Prod.ext h h₂⟩
  simp [negativePhaseDiagonal, Matrix.kronecker_apply, Matrix.diagonal_apply,
    Matrix.one_apply, h₂, h₁]

private theorem parityLayer_encodes_D :
    (q37ParityLayer (zPhase 8)).eval * q37CanonicalEncoding =
      q37CanonicalEncoding * (negativePhaseDiagonal 8 ⊗ₖ (1 : Operator (Fin 1))) := by
  rw [q37ParityLayer_eval, gaugeOne_diag]
  apply diagonal_mul_encoding_of_nonzero
  intro x b hx
  have h := q37Parity_count_nonzero x b hx
  apply (phase_pow_modEq (zPhase 8 : ℂ) (zPhase_pow 8 (by decide))
    (a := countOddBlocks q37ParitySupports x) (b := if b.1 = 0 then 0 else 7) (by split <;> simp_all)).trans
  split
  · simp
  · exact zPhase_pred 8 (by decide)

private theorem lineLayer_encodes_DualD :
    Matrix.diagonal (fun x => (zPhase 4 : ℂ) ^ countOddBlocks q37LineSupports x) *
      q37DualEncoding =
        q37DualEncoding * (negativePhaseDiagonal 4 ⊗ₖ (1 : Operator (Fin 1))) := by
  rw [gaugeOne_diag]
  apply diagonal_mul_encoding_of_nonzero
  intro x b hx
  have h := q37Line_count_nonzero x b hx
  apply (phase_pow_modEq (zPhase 4 : ℂ) (zPhase_pow 4 (by decide))
    (a := countOddBlocks q37LineSupports x) (b := if b.1 = 0 then 0 else 3) (by split <;> simp_all)).trans
  split
  · simp
  · exact zPhase_pred 4 (by decide)

private theorem negativePhaseDiagonal_eq_smul_rotationZ (m : ℕ) :
    negativePhaseDiagonal m = (Circle.exp (-Real.pi / m) : ℂ) •
      rotation SinglePauli.Z.matrix (Real.pi / m) := by
  let t := Real.pi / (m : ℝ)
  have hC (s : ℝ) : (Circle.exp s : ℂ) =
      (Real.cos s : ℂ) + (Real.sin s : ℂ) * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
  have hz (s : ℝ) : rotation SinglePauli.Z.matrix s =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (Circle.exp s : ℂ)
        else (Circle.exp (-s) : ℂ)) := by
    rw [show (fun i : Fin 2 => if i = 0 then (Circle.exp s : ℂ) else (Circle.exp (-s) : ℂ)) =
      (fun i : Fin 2 => if i = 0 then (Real.cos s : ℂ) + (Real.sin s : ℂ) * Complex.I
        else (Real.cos (-s) : ℂ) + (Real.sin (-s) : ℂ) * Complex.I) by
        funext i
        rw [hC, hC]]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, affine, SinglePauli.matrix, Matrix.one_apply, Matrix.diagonal_apply,
        smul_eq_mul, Real.cos_neg, Real.sin_neg] <;> ring
  have hAngle : -Real.pi / (m : ℝ) = -t := by unfold t; ring
  have hInv : (zPhase m : ℂ)⁻¹ = (Circle.exp (-(2 * t)) : ℂ) := by
    have ht : 2 * Real.pi / (m : ℝ) = 2 * t := by unfold t; ring
    rw [Circle.exp_neg, Circle.coe_inv, zPhase, ht]
  unfold negativePhaseDiagonal
  rw [hAngle, hz, hInv, ← Matrix.diagonal_smul]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i = 0
  · simp only [Pi.smul_apply, smul_eq_mul, ite_eq_left hi]
    rw [← Circle.coe_mul, ← Circle.exp_add, neg_add_cancel, Circle.exp_zero, Circle.coe_one]
  · simp only [Pi.smul_apply, smul_eq_mul, ite_eq_right hi]
    change (Circle.exp (-(2 * t)) : ℂ) = (Circle.exp (-t) : ℂ) * (Circle.exp (-t) : ℂ)
    rw [← Circle.coe_mul, ← Circle.exp_add, show -t + -t = -(2 * t) by ring]

private theorem hadamard_conjugates_rotationZ_matrix (s : ℝ) :
    hadamardMatrix * rotation SinglePauli.Z.matrix s * hadamardMatrix =
      rotation SinglePauli.X.matrix s := by
  simp only [rotation, affine, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hadamardMatrix_sq]
  rw [hadamard_conjugates_Z]

private theorem hadamardMatrix_isUnitary : IsUnitary hadamardMatrix := hadamardUnitary.property

/-- The two native Q37 layers have the required logical actions up to the
phase displayed on the physical-to-logical encoding equation. -/
theorem q37_parityLayer_logical_D :
    (q37ParityLayer (zPhase 8)).eval * q37CanonicalEncoding =
      q37CanonicalEncoding * (((Circle.exp (-Real.pi / 8) : ℂ) •
        rotation SinglePauli.Z.matrix (Real.pi / 8)) ⊗ₖ (1 : Operator (Fin 1))) := by
  rw [parityLayer_encodes_D, negativePhaseDiagonal_eq_smul_rotationZ]
  rfl

private theorem encodedConjugation {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (H Q : Operator I) (B D L : Operator J)
    (V V' : Matrix I J ℂ) (hHV : H * V = V' * L) (hHV' : H * V' = V * L)
    (hQV' : Q * V' = V' * D) (hLDL : L * D * L = B) :
    (H * Q * H) * V = V * B := by
  calc
    _ = H * (Q * (H * V)) := by simp only [Matrix.mul_assoc]
    _ = H * (Q * (V' * L)) := by rw [hHV]
    _ = H * ((Q * V') * L) := by rw [Matrix.mul_assoc]
    _ = H * ((V' * D) * L) := by rw [hQV']
    _ = (H * V') * D * L := by simp only [Matrix.mul_assoc]
    _ = (V * L) * D * L := by rw [hHV']
    _ = V * (L * D * L) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hLDL]

theorem q37_lineLayer_logical_B :
    (q37LineLayerInBasis (zPhase 4) (fun _ => hadamardMatrix)
      (fun _ => hadamardMatrix_isUnitary)).eval * q37CanonicalEncoding =
      q37CanonicalEncoding * (((Circle.exp (-Real.pi / 4) : ℂ) •
        rotation SinglePauli.X.matrix (Real.pi / 4)) ⊗ₖ (1 : Operator (Fin 1))) := by
  let H : Operator (QubitBasis 37) := physicalHadamard 37
  let Q : Operator (QubitBasis 37) :=
    Matrix.diagonal (fun x => (zPhase 4 : ℂ) ^ countOddBlocks q37LineSupports x)
  let V : Matrix (QubitBasis 37) (Fin 2 × Fin 1) ℂ := q37CanonicalEncoding
  let V' : Matrix (QubitBasis 37) (Fin 2 × Fin 1) ℂ := q37DualEncoding
  let L : Operator (Fin 2 × Fin 1) := hadamardMatrix ⊗ₖ (1 : Operator (Fin 1))
  let D : Operator (Fin 2 × Fin 1) := negativePhaseDiagonal 4 ⊗ₖ (1 : Operator (Fin 1))
  let B : Operator (Fin 2 × Fin 1) := ((Circle.exp (-Real.pi / 4) : ℂ) •
    rotation SinglePauli.X.matrix (Real.pi / 4)) ⊗ₖ (1 : Operator (Fin 1))
  have hL : L * L = 1 := by
    unfold L
    rw [← Matrix.mul_kronecker_mul, hadamardMatrix_sq, Matrix.one_mul,
      Matrix.one_kronecker_one]
  have hRight : H * V = V' * L := q37_physicalHadamard_transports_encoding
  have hSq : H * H = 1 := physicalHadamard_sq 37
  have hLeft : H * V' = V * L := by
    calc
      _ = H * (V' * L) * L := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one]
      _ = _ := by rw [← hRight, ← Matrix.mul_assoc, hSq, Matrix.one_mul]
  have hLDL : L * D * L = B := by
    unfold L D B
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
    congr 1
    rw [negativePhaseDiagonal_eq_smul_rotationZ, Matrix.mul_smul, Matrix.smul_mul,
      hadamard_conjugates_rotationZ_matrix]
    norm_num
  have hFold := q37LineLayerInBasis_eval (zPhase 4) (fun _ => hadamardMatrix)
    (fun _ => hadamardMatrix_isUnitary)
  have hGate : (q37LineLayerInBasis (zPhase 4) (fun _ => hadamardMatrix)
      (fun _ => hadamardMatrix_isUnitary)).eval = H * Q * H := by
    change _ = H * Q * H
    calc
      _ = H * Q * H.conjTranspose := hFold
      _ = _ := by rw [show H.conjTranspose = H from physicalHadamard_selfAdjoint 37]
  have hQV' : Q * V' = V' * D := lineLayer_encodes_DualD
  change _ * V = V * B
  exact (congrArg (fun M : Operator (QubitBasis 37) => M * V) hGate).trans
    (encodedConjugation H Q B D L V V' hRight hLeft hQV' hLDL)

/-- Exact encoded action up to a global scalar gives the same class in the
native positive-depth alphabet. -/
private theorem mem_depth_one_of_phase_encoding {n q : ℕ}
    (C : Code n (fun _ => 2) 2 1) (A : QubitOperator) (hA : IsUnitary A) (z : Circle)
    (L : Layer n (fun _ => 2) q)
    (hL : L.eval * C.encoding =
      C.encoding * (((z : ℂ) • A) ⊗ₖ (1 : Operator (Fin 1)))) :
    projectiveMk (Fin 2) ⟨A, hA⟩ ∈ nativeLogicalImage C.encoding q 1 := by
  let W : Matrix.unitaryGroup (Fin 2) ℂ :=
    ⟨(z : ℂ) • A, unitary_smul_of_phase (z : ℂ) A (circle_star_mul_self z) hA⟩
  have hm : projectiveMk (Fin 2) W = projectiveMk (Fin 2) ⟨A, hA⟩ :=
    (projectiveMk_eq_iff (Fin 2) W ⟨A, hA⟩).mpr ⟨z, circle_star_mul_self z, rfl⟩
  rw [← hm, nativeLogicalImage_eq_preimage C.encoding C.isometry,
    Set.mem_preimage, puToProjectiveOperator_mk]
  apply logicalImage_subset_atMost C q 1 _ le_rfl
  refine ⟨circuitOfLayers [L], W.val, ⟨W.property, 1, isUnitary_one, ?_⟩, rfl⟩
  rw [circuitOfLayers_eval]
  simpa [layerSequenceEval, W] using hL

set_option maxRecDepth 4096 in
theorem q37_projectiveD_mem_depth_one :
    projectiveD ∈ nativeLogicalImage q37CanonicalEncoding 3 1 := by
  exact mem_depth_one_of_phase_encoding q37CanonicalCode (rotation SinglePauli.Z.matrix (Real.pi / 8))
    (rotation_isUnitary (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) _)
    (Circle.exp (-Real.pi / 8)) (q37ParityLayer (zPhase 8)) q37_parityLayer_logical_D

set_option maxRecDepth 4096 in
theorem q37_projectiveB_mem_depth_one :
    projectiveB ∈ nativeLogicalImage q37CanonicalEncoding 3 1 := by
  exact mem_depth_one_of_phase_encoding q37CanonicalCode (rotation SinglePauli.X.matrix (Real.pi / 4))
    (rotation_isUnitary (singlePauli_selfAdjoint .X) (singlePauli_sq .X) _)
    (Circle.exp (-Real.pi / 4))
    (q37LineLayerInBasis (zPhase 4) (fun _ => hadamardMatrix) (fun _ => hadamardMatrix_isUnitary))
    q37_lineLayer_logical_B

#print axioms q37_projectiveD_mem_depth_one
#print axioms q37_projectiveB_mem_depth_one

#print axioms parityLayer_encodes_D
#print axioms lineLayer_encodes_DualD

end

end CriticalDepth.Q37BinaryData
