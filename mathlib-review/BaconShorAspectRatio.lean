import BaconShorShortTrace
import BaconShorXAxisNormalizer
import FaultDepthArithmetic

/-!
# Aspect-ratio lower bound for Bacon--Shor exact synthesis
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.Arithmetic
open CriticalDepth.FaultDepthArithmetic CriticalDepth.Manuscript20261114
open scoped ENat BigOperators Kronecker

noncomputable section

private theorem X_conjugate_of_mem_span (W : Operator (Fin 2)) (hW : IsUnitary W)
    (hspan : W * SinglePauli.X.matrix * star W ∈ logicalXAxisSpan) :
    W * SinglePauli.X.matrix * star W = SinglePauli.X.matrix ∨
      W * SinglePauli.X.matrix * star W = -SinglePauli.X.matrix := by
  let X := SinglePauli.X.matrix
  let T := W * X * star W
  change T ∈ Submodule.span ℂ ({1,X} : Set (Operator (Fin 2))) at hspan
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hspan
  have hx : X.trace = 0 := by
    simp [X, Matrix.trace, Matrix.diag, Fin.sum_univ_two, SinglePauli.matrix]
  have htr : T.trace = 0 := by
    unfold T
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW.1, Matrix.one_mul, hx]
  have hs : (a • (1 : Operator (Fin 2)) + b • X).trace = (2 : ℂ) * a := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hx, smul_zero, add_zero,
      Matrix.trace_one, Fintype.card_fin]
    simp [smul_eq_mul, mul_comm]
  have ha : a = 0 := by
    rw [hab, htr] at hs
    exact (mul_eq_zero.mp hs.symm).resolve_left (by norm_num)
  have hT : T = b • X := by
    rw [← hab, ha, zero_smul, zero_add]
  have hsq : T * T = 1 := by
    unfold T
    change (W * X * star W) * (W * X * star W) = 1
    calc
      _ = W * X * (star W * W) * X * star W := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hW.1, Matrix.mul_one, Matrix.mul_assoc W, singlePauli_sq, Matrix.mul_one, hW.2]
  have hb : b * b = 1 := by
    rw [hT, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hsq
    change (b*b) • (X * X) = 1 at hsq
    rw [show X * X = 1 from singlePauli_sq .X] at hsq
    have h := congrArg (fun M : Operator (Fin 2) => M 0 0) hsq
    simpa [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] using h
  have hc : (b-1)*(b+1)=0 := by linear_combination hb
  rcases mul_eq_zero.mp hc with h | h
  · left
    change T = X
    rw [hT, sub_eq_zero.mp h, one_smul]
  · right
    change T = -X
    rw [hT, eq_neg_of_add_eq_zero_left h, neg_one_smul]

variable {m b q : ℕ}

private theorem baconTrace_conjugated_X (U : Operator (QubitBasis ((m+1)*(b+1))))
    (W : Operator (Fin 2)) (hU : Implements (baconShorCode m b) U W)
    (hUUnit : IsUnitary U) :
    compressedGaugeTrace (baconShorCode m b)
        (U * pauliMatrix 0 (physicalXWord (fullXColumn (rows := m+1) (0 : Fin (b+1)))) *
          U.conjTranspose) = W * SinglePauli.X.matrix * star W := by
  let V := baconPhysicalEncoding m b
  let P := pauliMatrix 0 (physicalXWord (fullXColumn (rows := m+1) (0 : Fin (b+1))))
  let X := SinglePauli.X.matrix
  obtain ⟨hW,G,hG,he⟩ := hU
  change U * V = V * (W ⊗ₖ G) at he
  have hP : P * V = V * (X ⊗ₖ (1 : Operator (Fin (2^(m*b))))) :=
    baconPhysicalEncoding_bareX
  have hG' : G * G.conjTranspose = 1 := by exact hG.2
  have hPcomp : V.conjTranspose * P * V = X ⊗ₖ (1 : Operator (Fin (2^(m*b)))) := by
    rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc]
    change (baconPhysicalEncoding m b).conjTranspose * baconPhysicalEncoding m b * _ = _
    rw [baconPhysicalEncoding_isometric, Matrix.one_mul]
  have hUnit : U.conjTranspose * U = 1 := hUUnit.1
  have hBack : V.conjTranspose * U.conjTranspose * (U * P * U.conjTranspose) * U * V =
      X ⊗ₖ (1 : Operator (Fin (2^(m*b)))) := by
    calc
      _ = V.conjTranspose * (U.conjTranspose * U) * P * (U.conjTranspose * U) * V := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUnit, Matrix.mul_one, Matrix.mul_one, hPcomp]
  have hWt : W * W.conjTranspose = 1 := hW.2
  have hcomp : V.conjTranspose * (U * P * U.conjTranspose) * V =
      (W * X * star W) ⊗ₖ (1 : Operator (Fin (2^(m*b)))) := by
    rw [compressed_forward_of_backward _ _ _ _ _ he (kronecker_right_unitary W G hWt hG') hBack,
      conjTranspose_kronecker_operators, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hG']
    rfl
  change normalizedGaugeTrace (V.conjTranspose * (U * P * U.conjTranspose) * V) = _
  rw [hcomp, normalizedGaugeTrace_kronecker_one (by positivity)]

private theorem bacon_X_axis_of_normalizedCircuit {h : ℕ}
    (c : Circuit ((m+1)*(b+1)) (fun _ => 2) q h) (hq : 1 ≤ q) (hsize : (m+1)*q^h < b+1)
    (W : Matrix.unitaryGroup (Fin 2) ℂ)
    (himpl : Implements (baconShorCode m b) (circuitEval c) W.val) :
    preservesXAxis W := by
  let p := physicalXWord (fullXColumn (rows := m+1) (0 : Fin (b+1)))
  let L := List.ofFn c
  have hEval : layerSequenceEval L = circuitEval c := by
    rw [layerSequenceEval_eq_reverse_prod, List.map_ofFn]
    rfl
  have hP := layerSequence_conjugate_supportedOn L (pauliSupport p)
    (pauliMatrix_supportedOn_pauliSupport p)
  have hCard : (layerSequenceCone L (pauliSupport p)).card < b+1 := by
    apply (layerSequenceCone_card_le L _ hq).trans_lt
    rw [show L.length = h by simp [L],
      show (pauliSupport p).card = m+1 from fullXColumn_support_card _,
      mul_comm]
    exact hsize
  rw [hEval] at hP
  have ha := baconTrace_small_support_mem_XAxis _ hCard _ hP
  rw [baconTrace_conjugated_X _ _ himpl (point_circuitEval_isUnitary c)] at ha
  exact X_conjugate_of_mem_span W.val himpl.1 ha

theorem baconNativeLogicalImage_axis {h : ℕ}
    (hq : 1 ≤ q) (hsize : (m+1)*q^h < b+1) :
    nativeLogicalImage (baconShorCode m b).encoding q h ⊆ projectiveXAxisNormalizer := by
  intro u hu
  obtain ⟨r, hr, c, hc, W, G, henc, rfl⟩ := hu
  let C := baconShorCode m b
  let A := nativeToLegacyCircuit c hc
  have hImpl : Implements C (arbitraryCircuitEval A) W.val := by
    refine ⟨(isUnitary_iff_mem_unitaryGroup (Fin 2) W.val).mpr W.property, G.val,
      (isUnitary_iff_mem_unitaryGroup _ _).mpr G.property, ?_⟩
    rw [nativeToLegacyCircuit_eval]
    exact henc
  have hImpl' : Implements C (circuitEval A.normalized) W.val :=
    implements_of_projectivelyEquivalent_physical C (arbitraryCircuit_normalization_phase A) hImpl
  have hPow : q^r ≤ q^h := pow_le_pow_right' hq hr
  have hsmall : (m+1)*q^r < b+1 := (Nat.mul_le_mul_left _ hPow).trans_lt hsize
  exact ⟨W, bacon_X_axis_of_normalizedCircuit A.normalized hq hsmall W hImpl', rfl⟩

theorem baconShor_exactDepth_ratio_lower (hq : 2 ≤ q) :
    (Nat.clog q (ceilDiv (b+1) (m+1)) : ℕ∞) ≤ nativeExactDepth (baconShorCode m b).encoding q := by
  apply nativeExactDepth_lower_of_axis
  intro h hsmall
  apply baconNativeLogicalImage_axis (by omega)
  by_contra hb
  have hle : ceilDiv (b+1) (m+1) ≤ q^h :=
    (ceilDiv_le_iff _ _ _ (by omega)).mpr (by simpa [mul_comm] using (not_lt.mp hb))
  exact (not_le_of_gt hsmall) ((Nat.clog_le_iff_le_pow (by omega)).mpr hle)

#print axioms baconNativeLogicalImage_axis
#print axioms baconShor_exactDepth_ratio_lower

end

end CriticalDepth.FaultShorSaturation.BaconShor
