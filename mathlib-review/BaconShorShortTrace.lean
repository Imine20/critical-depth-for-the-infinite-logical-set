import BaconShorDressedDistance
import BaconShorGaugeTrace

/-!
# Gauge-traced Pauli expansion below the long side

For a Pauli supported on fewer sites than the long side, nonzero
gauge trace permits only column-constant X masks with zero Z mask.
The parity of the selected columns distinguishes identity and
protected X action.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript
open scoped BigOperators Kronecker

noncomputable section

variable {m b : ℕ}

def logicalXAxisSpan : Submodule ℂ (Operator (Fin 2)) :=
  Submodule.span ℂ ({1, SinglePauli.X.matrix} : Set (Operator (Fin 2)))

private theorem bit_ne_zero_eq_one (x : Bit) (hx : x ≠ 0) : x = 1 := by
  have h : ∀ t : Bit, t = 0 ∨ t = 1 := by decide
  exact (h x).resolve_left hx

private theorem baconBinaryEncoding_columnConstant_X
    (a : BaconMask m b) (hCol : ∀ j i k, a (i,j) = a (k,j))
    (x : BaconMask m b) (ℓ : Bit) (u : Interior m b) :
    baconBinaryEncoding m b (x + a) (ℓ,u) =
      baconBinaryEncoding m b x (ℓ + rowParity a 0, u) := by
  have selfAdd (y : BaconMask m b) : y + y = 0 := by
    funext i
    have h : ∀ t : Bit, t + t = 0 := by decide
    exact h (y i)
  have hpar (i : Fin (m+1)) : rowParity a i = rowParity a 0 := by
    unfold rowParity
    exact Finset.sum_congr rfl (fun j _ => hCol j i 0)
  have hshift (k : Bit) (t : CenterCoordinate b) :
      baconWord k u t + a = baconWord (k + rowParity a 0) u (t + topBits a) := by
    let y := baconWord k u t + a
    have hp (i : Fin (m+1)) : rowParity y i = k + rowParity a 0 := by
      have h : rowParity y i = rowParity (baconWord k u t) i + rowParity a i := by
        simp [y, rowParity, Pi.add_apply, Finset.sum_add_distrib]
      rw [h, baconWord_rowParity, hpar]
    have hh := congrArg Subtype.val ((baconWordEquiv (m := m) (b := b)).apply_symm_apply
      ⟨y, fun i => (hp i).trans (hp 0).symm⟩)
    change baconWord (rowParity y 0) (gaugeBits y) (topBits y) = y at hh
    have hg : gaugeBits a = 0 := by
      funext i j
      change a (i.succ, j.succ) - a (0,j.succ) = 0
      rw [hCol j.succ i.succ 0, sub_self]
    have hu : gaugeBits y = u := by
      change gaugeBits (baconWord k u t + a) = _
      rw [gaugeBits_add, baconWord_gaugeBits, hg, add_zero]
    rw [hp, hu] at hh
    exact hh.symm
  have hm : x + a ∈ orbitWords ℓ u ↔ x ∈ orbitWords (ℓ + rowParity a 0) u := by
    rw [orbitWords_mem, orbitWords_mem]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t + topBits a, ?_⟩
      rw [← hshift, ht, add_assoc, selfAdd, add_zero]
    · rintro ⟨t, ht⟩
      refine ⟨t + topBits a, ?_⟩
      rw [← ht, hshift, add_assoc ℓ]
      have h : ∀ t : Bit, t + t = 0 := by decide
      rw [h, add_zero]
  simp only [baconBinaryEncoding, hm]

private theorem baconPhysicalEncoding_columnConstant_X
    (a : BaconMask m b) (hCol : ∀ j i k, a (i,j) = a (k,j)) :
    pauliMatrix 0 (physicalXWord a) * baconPhysicalEncoding m b =
      if rowParity a 0 = 0 then baconPhysicalEncoding m b else
        pauliMatrix 0 (physicalXWord (fullXColumn (rows := m+1) (0 : Fin (b+1)))) *
          baconPhysicalEncoding m b := by
  ext x j
  let E := shorBasisEquiv (m+1) (b+1)
  let w : BaconMask m b → ℂ :=
    fun y => baconBinaryEncoding m b y (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2)
  change (pauliMatrix 0 (physicalXWord a)).mulVec (w ∘ E) x = _
  rw [physicalXWord_mulVec, shorXCheck_mulVec]
  by_cases h : rowParity a 0 = 0
  · rw [ite_eq_left h]
    change baconBinaryEncoding m b (E x + a) (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2) = _
    rw [baconBinaryEncoding_columnConstant_X a hCol, h, add_zero]
    rfl
  · rw [ite_eq_right h]
    change baconBinaryEncoding m b (E x + a) (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2) =
      (pauliMatrix 0 (physicalXWord (fullXColumn (rows := m+1) (0 : Fin (b+1))))).mulVec
        (w ∘ E) x
    rw [physicalXWord_mulVec, shorXCheck_mulVec]
    change baconBinaryEncoding m b (E x + a) (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2) =
      baconBinaryEncoding m b (E x + fullXColumn 0) (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2)
    rw [baconBinaryEncoding_columnConstant_X a hCol, baconBinaryEncoding_bareX,
      bit_ne_zero_eq_one _ h]

private theorem encodedGaugeFactorUnitary {n K g : ℕ} (C : Code n (fun _ => 2) K g)
    (hK : 0 < K) (p : Fin n → SinglePauli) (G : Operator (Fin g))
    (hP : pauliMatrix 0 p * C.encoding = C.encoding * ((1 : Operator (Fin K)) ⊗ₖ G)) :
    G.conjTranspose * G = 1 := by
  let V := C.encoding
  let P := pauliMatrix 0 p
  let T := (1 : Operator (Fin K)) ⊗ₖ G
  have hunit : P.conjTranspose * P = 1 := (unphased_pauliMatrix_isUnitary p).1
  have hAdj : (P * V).conjTranspose * (P * V) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P.conjTranspose,
      hunit, Matrix.one_mul, show V.conjTranspose * V = 1 from C.isometry]
  change P * V = V * T at hP
  rw [hP, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V.conjTranspose,
    C.isometry, Matrix.one_mul] at hAdj
  have hTensor : (1 : Operator (Fin K)) ⊗ₖ (G.conjTranspose * G) = 1 := by
    change (((1 : Operator (Fin K)) ⊗ₖ G).conjTranspose) *
      ((1 : Operator (Fin K)) ⊗ₖ G) = _ at hAdj
    rw [conjTranspose_kronecker_operators, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul] at hAdj
    exact hAdj
  ext u v
  let k : Fin K := ⟨0, hK⟩
  have he := congrArg (fun M : Operator (Fin K × Fin g) => M (k,u) (k,v)) hTensor
  change ((1 : Operator (Fin K)) ⊗ₖ (G.conjTranspose * G)) (k,u) (k,v) =
    (1 : Operator (Fin K × Fin g)) (k,u) (k,v) at he
  simpa [Matrix.kronecker_apply, Matrix.one_apply, Prod.mk.injEq] using he

private theorem gaugeTrace_antipauli (p q : Fin ((m+1)*(b+1)) → SinglePauli)
    (G : Operator (Fin (2 ^ (m*b))))
    (hQ : pauliMatrix 0 q * baconPhysicalEncoding m b =
      baconPhysicalEncoding m b * ((1 : Operator (Fin 2)) ⊗ₖ G))
    (hAnti : pauliMatrix 0 q * pauliMatrix 0 p = -(pauliMatrix 0 p * pauliMatrix 0 q)) :
    compressedGaugeTrace (baconShorCode m b) (pauliMatrix 0 p) = 0 := by
  let C : Code ((m+1)*(b+1)) (fun _ => 2) 2 (2^(m*b)) := baconShorCode m b
  let P : Operator (QubitBasis ((m+1)*(b+1))) := pauliMatrix 0 p
  let Q : Operator (QubitBasis ((m+1)*(b+1))) := pauliMatrix 0 q
  change Q * C.encoding = C.encoding * ((1 : Operator (Fin 2)) ⊗ₖ G) at hQ
  have hself : Q.conjTranspose = Q := unphased_pauliMatrix_selfAdjoint q
  have hg : G.conjTranspose * G = 1 := encodedGaugeFactorUnitary C (by decide) q G hQ
  have ha : Q*P*Q = -P := by
    change Q*P = -(P*Q) at hAnti
    rw [hAnti, Matrix.neg_mul, Matrix.mul_assoc, show Q*Q = 1 from unphased_pauliMatrix_sq q,
      Matrix.mul_one]
  exact compressedGaugeTrace_eq_zero_of_anticommutes_with_gauge C P Q G hQ hself hg ha

theorem baconTrace_small_pauli_mem_XAxis (p : Fin ((m+1)*(b+1)) → SinglePauli)
    (hp : (pauliSupport p).card < b+1) :
    compressedGaugeTrace (baconShorCode m b) (pauliMatrix 0 p) ∈ logicalXAxisSpan := by
  let C := baconShorCode m b
  let x := xMaskOfPauli (rows := m+1) (columns := b+1) p
  let z := zMaskOfPauli (rows := m+1) (columns := b+1) p
  have hs : (support x z).card < b+1 :=
    (pauliSupport_card_eq_rectangular (rows := m+1) (columns := b+1) p) ▸ hp
  by_cases hX : ∀ a, gaugeX a → maskDot z a = 0
  · by_cases hZ : ∀ a, gaugeZ a → maskDot x a = 0
    · obtain ⟨hcol, hrow⟩ := (bareCentralizes_iff x z).mp ⟨hX,hZ⟩
      have hz0 : z = 0 := by
        funext ij
        by_contra h
        exact (not_lt_of_ge (bare_Z_row_weight_bound x z ⟨hX,hZ⟩ ij.1 ij.2 h)) hs
      have hzword : physicalZWord z = fun _ => SinglePauli.I := by
        funext i
        simp [hz0, physicalZWord]
      have hZR : pauliMatrix 0 (physicalZWord z) = 1 := by
        rw [hzword, pauliMatrix_zero_eq_tensorEntries]
        exact tensorEntries_one
      rw [pauliMatrix_eq_physicalXZ (rows := m+1) (columns := b+1) p]
      change compressedGaugeTrace C (_ • (pauliMatrix 0 (physicalXWord x) *
        pauliMatrix 0 (physicalZWord z))) ∈ _
      rw [hZR, Matrix.mul_one, map_smul]
      apply logicalXAxisSpan.smul_mem
      have hn : 0 < 2 ^ (m*b) := by positivity
      have hx := baconPhysicalEncoding_columnConstant_X x hcol
      by_cases ht : rowParity x 0 = 0
      · rw [ite_eq_left ht] at hx
        have htrace : compressedGaugeTrace C (pauliMatrix 0 (physicalXWord x)) = 1 := by
          change normalizedGaugeTrace ((baconPhysicalEncoding m b).conjTranspose *
            pauliMatrix 0 (physicalXWord x) * baconPhysicalEncoding m b) = _
          rw [Matrix.mul_assoc, hx, baconPhysicalEncoding_isometric, ← Matrix.one_kronecker_one,
            normalizedGaugeTrace_kronecker_one hn]
        rw [htrace]
        exact Submodule.subset_span (by simp)
      · rw [ite_eq_right ht, baconPhysicalEncoding_bareX] at hx
        have htrace : compressedGaugeTrace C (pauliMatrix 0 (physicalXWord x)) = SinglePauli.X.matrix := by
          change normalizedGaugeTrace ((baconPhysicalEncoding m b).conjTranspose *
            pauliMatrix 0 (physicalXWord x) * baconPhysicalEncoding m b) = _
          rw [Matrix.mul_assoc, hx, ← Matrix.mul_assoc, baconPhysicalEncoding_isometric,
            Matrix.one_mul, normalizedGaugeTrace_kronecker_one hn]
        rw [htrace]
        exact Submodule.subset_span (by simp)
    · push Not at hZ
      obtain ⟨a, ha, hne⟩ := hZ
      have hanti := physicalZ_commutation a p
      change _ = pauliParitySign (maskDot x a) • _ at hanti
      simp only [pauliParitySign, ite_eq_right hne, neg_one_smul] at hanti
      rw [gaugeTrace_antipauli p (physicalZWord a) _ (baconPhysicalEncoding_gaugeZ a ha) hanti]
      exact Submodule.zero_mem _
  · push Not at hX
    obtain ⟨a, ha, hne⟩ := hX
    have hanti := physicalX_commutation a p
    change _ = pauliParitySign (maskDot z a) • _ at hanti
    simp only [pauliParitySign, ite_eq_right hne, neg_one_smul] at hanti
    rw [gaugeTrace_antipauli p (physicalXWord a) _ (baconPhysicalEncoding_gaugeX a ha) hanti]
    exact Submodule.zero_mem _

theorem baconTrace_small_support_mem_XAxis
    (S : Finset (Fin ((m+1)*(b+1)))) (hS : S.card < b+1)
    (O : Operator (QubitBasis ((m+1)*(b+1)))) (hO : SupportedOn O S) :
    compressedGaugeTrace (baconShorCode m b) O ∈ logicalXAxisSpan := by
  classical
  obtain ⟨A, hA⟩ := hO
  let T := (compressedGaugeTrace (baconShorCode m b)).comp (localEmbedLinearMap S)
  have hspan : pauliTensorSpan S ≤ logicalXAxisSpan.comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change compressedGaugeTrace (baconShorCode m b) (localEmbed S (tensorPauli p)) ∈ logicalXAxisSpan
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    apply baconTrace_small_pauli_mem_XAxis
    have hsub : pauliSupport (extendLocalPauli S p) ⊆ S := by
      apply pauliSupport_subset_of_outside_identity
      intro i hi
      simp [extendLocalPauli, hi]
    exact (Finset.card_le_card hsub).trans_lt hS
  rw [tensorPauli_span_eq_top] at hspan
  have h : compressedGaugeTrace (baconShorCode m b) (localEmbed S A) ∈ logicalXAxisSpan :=
    hspan (show A ∈ (⊤ : Submodule ℂ (Operator (LocalBasis (fun _ : Fin ((m+1)*(b+1)) => 2) S))) from trivial)
  simpa only [hA] using h

#print axioms baconTrace_small_pauli_mem_XAxis
#print axioms baconTrace_small_support_mem_XAxis

end

end CriticalDepth.FaultShorSaturation.BaconShor
