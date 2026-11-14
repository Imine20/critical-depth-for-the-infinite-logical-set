import BaconShorGaugeActions
import ShorPhysicalXLogical

/-!
# Exact dressed distance of the rectangular Bacon--Shor code
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript
open scoped BigOperators Kronecker

noncomputable section

variable {m b : ℕ}

private theorem baconPhysicalEncoding_centerX (a : BaconMask m b) (ha : centerX a) :
    pauliMatrix 0 (physicalXWord a) * baconPhysicalEncoding m b = baconPhysicalEncoding m b := by
  have h := (centerX_iff a 0).mp ha
  have hg : gaugeBits a = 0 := by
    funext i j
    change a (i.succ,j.succ) - a (0,j.succ) = 0
    rw [h.2 j.succ i.succ 0, sub_self]
  ext x j
  let e := shorBasisEquiv (m + 1) (b + 1)
  let f : BaconMask m b → ℂ :=
    fun y => baconBinaryEncoding m b y (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2)
  change (pauliMatrix 0 (physicalXWord a)).mulVec (f ∘ e) x = _
  rw [physicalXWord_mulVec, shorXCheck_mulVec]
  change baconBinaryEncoding m b (e x + a) (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2) =
    baconBinaryEncoding m b (e x) (qubitBitEquiv j.1, gaugeTupleEquiv m b j.2)
  rw [baconBinaryEncoding_gaugeX a h.1, hg, add_zero]

private theorem baconPhysicalEncoding_centerZ (z : BaconMask m b) (hz : centerZ z) :
    pauliMatrix 0 (physicalZWord z) * baconPhysicalEncoding m b = baconPhysicalEncoding m b := by
  classical
  ext x j
  let e := shorBasisEquiv (m + 1) (b + 1)
  let ℓ := qubitBitEquiv j.1
  let u := gaugeTupleEquiv m b j.2
  change (pauliMatrix 0 (physicalZWord z)).mulVec (fun y => baconPhysicalEncoding m b y j) x = _
  rw [physicalZWord_mulVec]
  change (if maskDot (e x) z = 0 then (1 : ℂ) else -1) * baconBinaryEncoding m b (e x) (ℓ,u) =
    baconBinaryEncoding m b (e x) (ℓ,u)
  by_cases hx : e x ∈ orbitWords ℓ u
  · obtain ⟨t, ht⟩ := (orbitWords_mem _ _ _).mp hx
    obtain ⟨r, hr, hzr⟩ := hz
    have hp : maskDot (baconWord ℓ u t) z = 0 := by
      rw [hzr]
      simp only [maskDot, Fintype.sum_prod_type, repeatRows, ← Finset.sum_mul]
      change (∑ i, rowParity (baconWord ℓ u t) i * r i) = 0
      simp_rw [baconWord_rowParity]
      rw [← Finset.mul_sum, hr, mul_zero]
    rw [← ht]
    rw [if_pos hp, one_mul]
  · simp [baconBinaryEncoding, hx]

theorem baconSmallPauli_gaugeOnly (p : Fin ((m+1)*(b+1)) → SinglePauli)
    (hp : (pauliSupport p).card < min (m+1) (b+1)) :
    GaugeOnly (baconShorCode m b) (pauliMatrix 0 p) := by
  let C := baconShorCode m b
  let x := xMaskOfPauli (rows := m+1) (columns := b+1) p
  let z := zMaskOfPauli (rows := m+1) (columns := b+1) p
  have hwt : (support x z).card < min (m+1) (b+1) :=
    (pauliSupport_card_eq_rectangular (rows := m+1) (columns := b+1) p) ▸ hp
  by_cases hX : ∀ a, centerX a → maskDot z a = 0
  · by_cases hZ : ∀ a, centerZ a → maskDot x a = 0
    · obtain ⟨ha, hz⟩ := dressed_below_short_side x z ⟨hX, hZ⟩ hwt
      rw [pauliMatrix_eq_physicalXZ (rows := m+1) (columns := b+1) p]
      change _ ∈ gaugeOnlyComplexSubmodule C
      apply (gaugeOnlyComplexSubmodule C).smul_mem
      exact baconGaugeOnly_XZ x z ha hz
    · push Not at hZ
      obtain ⟨a, ha, hne⟩ := hZ
      have hanti := physicalZ_commutation a p
      change _ = pauliParitySign (maskDot x a) • _ at hanti
      simp only [pauliParitySign, ite_eq_right hne, neg_one_smul] at hanti
      exact anticommuting_fixed_operator_gaugeOnly C _ _
        (unphased_pauliMatrix_isUnitary _) (baconPhysicalEncoding_centerZ a ha) hanti
  · push Not at hX
    obtain ⟨a, ha, hne⟩ := hX
    have hanti := physicalX_commutation a p
    change _ = pauliParitySign (maskDot z a) • _ at hanti
    simp only [pauliParitySign, ite_eq_right hne, neg_one_smul] at hanti
    exact anticommuting_fixed_operator_gaugeOnly C _ _
      (unphased_pauliMatrix_isUnitary _) (baconPhysicalEncoding_centerX a ha) hanti

theorem baconShorCode_detectsBelow :
    DetectsBelow (baconShorCode m b) (min (m+1) (b+1)) := by
  classical
  let C := baconShorCode m b
  intro S hS O hO
  obtain ⟨A, hA⟩ := hO
  let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin ((m+1)*(b+1)) => 2) S)) :=
    (gaugeOnlyComplexSubmodule C).comap (localEmbedLinearMap S)
  have hspan : pauliTensorSpan S ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change GaugeOnly C (localEmbed S (tensorPauli p))
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    apply baconSmallPauli_gaugeOnly
    have hsub : pauliSupport (extendLocalPauli S p) ⊆ S := by
      apply pauliSupport_subset_of_outside_identity
      intro i hi
      simp [extendLocalPauli, hi]
    exact (Finset.card_le_card hsub).trans_lt hS
  rw [tensorPauli_span_eq_top] at hspan
  have hAB : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
  change GaugeOnly C (localEmbed S A) at hAB
  simpa only [hA] using hAB

theorem baconShorCode_hasActualDistance (hmb : m ≤ b) :
    HasActualDistance (baconShorCode m b) (m+1) := by
  let p := physicalXWord (fullXColumn (rows := m+1) (0 : Fin (b+1)))
  let C := baconShorCode m b
  refine ⟨?_, pauliSupport p, fullXColumn_support_card (0 : Fin (b+1)), pauliMatrix 0 p,
    pauliMatrix_supportedOn_pauliSupport p, ?_⟩
  · simpa [Nat.min_eq_left (Nat.succ_le_succ hmb)] using
      (baconShorCode_detectsBelow (m := m) (b := b))
  · rintro ⟨G, hG⟩
    have hr : C.encoding.conjTranspose * pauliMatrix 0 p * C.encoding =
        SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin (2 ^ (m*b)))) := by
      change (baconPhysicalEncoding m b).conjTranspose * pauliMatrix 0 p *
        baconPhysicalEncoding m b = _
      rw [Matrix.mul_assoc, show pauliMatrix 0 p * baconPhysicalEncoding m b = _
        from baconPhysicalEncoding_bareX, ← Matrix.mul_assoc,
        baconPhysicalEncoding_isometric, Matrix.one_mul]
    rw [hr] at hG
    let a : Fin (2 ^ (m*b)) := ⟨0, by positivity⟩
    have h := congrArg (fun A : Operator (Fin 2 × Fin (2 ^ (m*b))) => A (0,a) (1,a)) hG
    change (SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin (2 ^ (m*b))))) (0,a) (1,a) =
      ((1 : Operator (Fin 2)) ⊗ₖ G) (0,a) (1,a) at h
    norm_num [Matrix.kronecker_apply, Matrix.one_apply, SinglePauli.matrix] at h

#print axioms baconShorCode_detectsBelow
#print axioms baconShorCode_hasActualDistance

end

end CriticalDepth.FaultShorSaturation.BaconShor
