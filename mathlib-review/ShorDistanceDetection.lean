import ShorStabilizer
import ShorPauliMasks

/-!
# Error detection for the physical rectangular Shor code

A nonzero binary dot product with a check makes the Pauli anticommute
with a check fixing the encoding. Otherwise its binary masks obey the
centralizer equations. Below the shorter rectangle side, its X mask
is a check and its Z mask is zero.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.PauliGroup CriticalDepth.ReviewV2
open scoped BigOperators Kronecker

variable {rows columns : ℕ}

private theorem zeroPauliZWord : physicalZWord (0 : Mask rows columns) =
    fun _ => SinglePauli.I := by
  funext s
  simp [physicalZWord]

private theorem bit_eq_of_add_eq_zero (x y : Bit) (h : x + y = 0) : x = y := by
  have htwo (a : Bit) : a + a = 0 := by decide +revert
  have hh := congrArg (fun z => x + z) h
  simpa only [← add_assoc, htwo, zero_add, add_zero] using hh.symm

private theorem no_binary_syndrome_centralizes (x z : Mask rows columns)
    (hX : ∀ a, xChecks a → maskDot z a = 0)
    (hZ : ∀ i j : Fin rows, maskDot x (rowPairZMask i j) = 0) (r : Fin rows) :
    centralizes x z := by
  have hparity (i j : Fin rows) : rowParity x i = rowParity x j := by
    have hz := hZ i j
    rw [maskDot_rowPairZMask] at hz
    exact bit_eq_of_add_eq_zero _ _ hz
  have hZall : ∀ a, zChecks a → maskDot x a = 0 := by
    rintro a ⟨b, hb, rfl⟩
    simp only [maskDot, Fintype.sum_prod_type, repeatRows, ← Finset.sum_mul]
    change (∑ i : Fin rows, rowParity x i * b i) = 0
    calc
      (∑ i : Fin rows, rowParity x i * b i) =
          ∑ i : Fin rows, rowParity x r * b i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hparity i r]
      _ = 0 := by rw [← Finset.mul_sum, hb, mul_zero]
  exact ⟨hX, hZall⟩

theorem physicalShorCode_smallPauli_gaugeOnly (r : Fin rows)
    (p : Fin (rows * (columns + 1)) → SinglePauli)
    (hp : (pauliSupport p).card < min rows (columns + 1)) :
    GaugeOnly (physicalShorCode (columns := columns) r) (pauliMatrix 0 p) := by
  classical
  let C := physicalShorCode (columns := columns) r
  let x := xMaskOfPauli (rows := rows) (columns := columns + 1) p
  let z := zMaskOfPauli (rows := rows) (columns := columns + 1) p
  change GaugeOnly C (pauliMatrix 0 p)
  have hwt : (support x z).card < min rows (columns + 1) := by
    exact (pauliSupport_card_eq_rectangular (rows := rows) (columns := columns + 1) p) ▸ hp
  have hfixX (a : Mask rows (columns + 1)) (ha : xChecks a) :
      pauliMatrix 0 (physicalXWord a) * C.encoding = C.encoding :=
    physicalShorEncoding_xCheck_fixes r a ha
  have hfixZ (i j : Fin rows) :
      pauliMatrix 0 (physicalZWord (rowPairZMask (columns := columns + 1) i j)) *
        C.encoding = C.encoding :=
    physicalShorEncoding_zPair_fixes r i j
  by_cases hX : ∀ a, xChecks a → maskDot z a = 0
  · by_cases hZ : ∀ i j : Fin rows, maskDot x (rowPairZMask i j) = 0
    · have hC := no_binary_syndrome_centralizes x z hX hZ r
      have hx := (below_min_distance_trivial x z hC hwt).1
      have hz : z = 0 := by
        funext ij
        have hc := (centralizes_iff x z).mp hC
        by_contra hne
        exact (not_lt_of_ge (columns_le_support_of_nonzero_entry x z hc.1 ij.1 ij.2 hne))
          (hwt.trans_le (min_le_right _ _))
      rw [pauliMatrix_eq_physicalXZ (rows := rows) (columns := columns + 1) p]
      change GaugeOnly C (_ •
        (pauliMatrix 0 (physicalXWord x) * pauliMatrix 0 (physicalZWord z)))
      rw [hz, zeroPauliZWord]
      have hId : pauliMatrix 0 (fun _ : Fin (rows * (columns + 1)) => SinglePauli.I) = 1 := by
        rw [pauliMatrix_zero_eq_tensorEntries]
        exact tensorEntries_one
      rw [hId, Matrix.mul_one]
      apply (gaugeOnlyComplexSubmodule C).smul_mem
      change GaugeOnly C (pauliMatrix 0 (physicalXWord x))
      refine ⟨1, ?_⟩
      rw [Matrix.mul_assoc, hfixX x hx, C.isometry]
      simp
    · push Not at hZ
      obtain ⟨i, j, hij⟩ := hZ
      have hanti := physicalZ_commutation (rowPairZMask i j) p
      change _ = pauliParitySign (maskDot x (rowPairZMask i j)) • _ at hanti
      simp only [pauliParitySign, ite_eq_right hij, neg_one_smul] at hanti
      exact anticommuting_fixed_operator_gaugeOnly C _ _
        (unphased_pauliMatrix_isUnitary _) (hfixZ i j) hanti
  · push Not at hX
    obtain ⟨a, ha, hne⟩ := hX
    have hanti := physicalX_commutation a p
    change _ = pauliParitySign (maskDot z a) • _ at hanti
    simp only [pauliParitySign, ite_eq_right hne, neg_one_smul] at hanti
    exact anticommuting_fixed_operator_gaugeOnly C _ _
      (unphased_pauliMatrix_isUnitary _) (hfixX a ha) hanti

theorem physicalShorCode_detectsBelow (r : Fin rows) :
    DetectsBelow (physicalShorCode (columns := columns) r) (min rows (columns + 1)) := by
  classical
  let C := physicalShorCode (columns := columns) r
  intro S hS O hO
  obtain ⟨A, hA⟩ := hO
  let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin (rows * (columns + 1)) => 2) S)) :=
    (gaugeOnlyComplexSubmodule C).comap (localEmbedLinearMap S)
  have hspan : pauliTensorSpan S ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change GaugeOnly C (localEmbed S (tensorPauli p))
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    apply physicalShorCode_smallPauli_gaugeOnly r
    have hsub : pauliSupport (extendLocalPauli S p) ⊆ S := by
      apply pauliSupport_subset_of_outside_identity
      intro i hi
      simp [extendLocalPauli, hi]
    exact (Finset.card_le_card hsub).trans_lt hS
  rw [tensorPauli_span_eq_top] at hspan
  have hAB : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
  change GaugeOnly C (localEmbed S A) at hAB
  simpa only [hA] using hAB

#print axioms physicalShorCode_smallPauli_gaugeOnly
#print axioms physicalShorCode_detectsBelow

end CriticalDepth.FaultShorSaturation
