import BaconShorDressedDistance
import OneQubitBareSynthesis

/-!
# Bacon--Shor continuous onset and upper exact-synthesis depth
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114 CriticalDepth.Manuscript20261114.OneQubitEuler
open scoped ENat Kronecker

noncomputable section

variable {m b : ℕ}

theorem baconPhysicalZRow_weight (i : Fin (m + 1)) :
    (pauliSupport (physicalZWord (fullZRow (columns := b + 1) i))).card = b + 1 := by
  classical
  let e := shorSiteEquiv (m + 1) (b + 1)
  let z := fullZRow (columns := b + 1) i
  let p := physicalZWord z
  have hs : (pauliSupport p).map e.toEmbedding =
      support (0 : BaconMask m b) z := by
    ext j
    obtain ⟨a, rfl⟩ := e.surjective j
    rw [Finset.mem_map_equiv]
    rw [show e.symm (e a) = a from e.symm_apply_apply a]
    change a ∈ Finset.univ.filter (fun i => p i ≠ .I) ↔
      e a ∈ Finset.univ.filter (fun ij => (0 : BaconMask m b) ij ≠ 0 ∨ z ij ≠ 0)
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Pi.zero_apply, ne_eq, not_true_eq_false, false_or]
    change (if z (e a) = 0 then SinglePauli.I else .Z) ≠ .I ↔ z (e a) ≠ 0
    by_cases h : z (e a) = 0 <;> simp [h]
  calc
    (pauliSupport p).card = ((pauliSupport p).map e.toEmbedding).card := by rw [Finset.card_map]
    _ = (support (0 : BaconMask m b) z).card := congrArg Finset.card hs
    _ = b + 1 := fullZRow_weight i

private theorem logicalX_nonscalar : ¬ IsScalar SinglePauli.X.matrix := by
  rintro ⟨z, h⟩
  have hh := congrArg (fun T : Operator (Fin 2) => T 0 1) h
  change SinglePauli.X.matrix 0 1 = (z • (1 : Operator (Fin 2))) 0 1 at hh
  norm_num [SinglePauli.matrix, Matrix.one_apply] at hh

theorem baconShor_nativeCriticalDepth (hm : 1 ≤ m) (hmb : m ≤ b) (q : ℕ) (hq : 2 ≤ q) :
    nativeCriticalDepth (baconShorCode m b).encoding q = (criticalDepth q (m + 1) : ℕ∞) := by
  let C := baconShorCode m b
  let d := criticalDepth q (m + 1)
  have hdet : DetectsBelow C (m + 1) := (baconShorCode_hasActualDistance hmb).1
  have hg : 1 ≤ 2 ^ (m * b) := Nat.succ_le_of_lt (by positivity : 0 < 2 ^ (m*b))
  have hn : 1 ≤ (m + 1) * (b + 1) := Nat.succ_le_of_lt (by positivity : 0 < (m+1)*(b+1))
  have hd : 1 ≤ d := criticalDepth_positive_of_two_ge q (m + 1) hq (by omega)
  apply le_antisymm
  · apply (nativeCriticalDepth_le_nat_iff C.encoding q d).mpr
    refine ⟨hd, ?_⟩
    let p := physicalXWord (fullXColumn (rows := m + 1) (0 : Fin (b + 1)))
    have hp : (pauliSupport p).card = m + 1 := fullXColumn_support_card 0
    have hsub := barePauli_circle_subset_nativeLogicalImage C (by omega) q hq p
      SinglePauli.X.matrix baconPhysicalEncoding_bareX
      (singlePauli_selfAdjoint .X) (singlePauli_sq .X)
    rw [hp, max_eq_right hd] at hsub
    let S := circleRotationSubgroup SinglePauli.X.matrix
      (singlePauli_selfAdjoint .X) (singlePauli_sq .X)
    have hf : (S : Set (PU (Fin 2))).Infinite := by
      let e := circleRotationEquiv (P := SinglePauli.X.matrix)
        (singlePauli_selfAdjoint .X) (singlePauli_sq .X) logicalX_nonscalar
      have hParam : Function.Injective (fun x : ℝ => Circle.exp (Real.arctan x)) := by
        intro x y hxy
        apply Real.arctan_injective
        have hbound : Real.pi / 2 - -(Real.pi / 2) < 2 * Real.pi := by
          linarith [Real.pi_pos]
        exact Circle.exp_injOn_Icc hbound
          (Set.Ioo_subset_Icc_self (Real.arctan_mem_Ioo x))
          (Set.Ioo_subset_Icc_self (Real.arctan_mem_Ioo y)) hxy
      letI : Infinite Circle := Infinite.of_injective _ hParam
      letI : Infinite S := Infinite.of_injective e e.injective
      exact Set.infinite_coe_iff.mp inferInstance
    exact hf.mono hsub
  · unfold nativeCriticalDepth
    apply le_sInf
    rintro _ ⟨h, hp, rfl, hinf⟩
    apply ENat.natCast_le_natCast.mpr
    by_contra hb
    have hfinite := (nativeTheoremOne_proved _ 2 _ (m + 1) (fun _ => 2)
      hn le_rfl hg (by omega) C.encoding C.isometry hdet q h hq hp (by omega)).1
    exact hinf hfinite

theorem baconShor_nativeExactDepth_upper (hm : 1 ≤ m) (hmb : m ≤ b)
    (q : ℕ) (hq : 2 ≤ q) :
    nativeExactDepth (baconShorCode m b).encoding q ≤ (criticalDepth q (b + 1) : ℕ∞) := by
  let C := baconShorCode m b
  let pX := physicalXWord (fullXColumn (rows := m + 1) (0 : Fin (b + 1)))
  let pZ := physicalZWord (fullZRow (columns := b + 1) (0 : Fin (m + 1)))
  have h := nativeExactDepth_le_of_bare_XZ C (by positivity) q hq pX pZ
    baconPhysicalEncoding_bareX (baconPhysicalEncoding_bareZ 0)
  have hXweight : (pauliSupport pX).card = m+1 := fullXColumn_support_card 0
  have hZweight : (pauliSupport pZ).card = b+1 := baconPhysicalZRow_weight 0
  rw [hXweight, hZweight] at h
  have hdepth : 1 ≤ criticalDepth q (m + 1) :=
    criticalDepth_positive_of_two_ge q (m + 1) hq (by omega)
  have horder : criticalDepth q (m + 1) ≤ criticalDepth q (b + 1) :=
    criticalDepth_mono_weight q (by omega)
  simpa [max_eq_right hdepth, max_eq_right (hdepth.trans horder), max_eq_right horder] using h

theorem baconShor_equal_thresholds_of_shell (hm : 1 ≤ m) (hmb : m ≤ b)
    (q : ℕ) (hq : 2 ≤ q) (hshell : b + 1 ≤ q ^ Nat.clog q (m + 1)) :
    nativeExactDepth (baconShorCode m b).encoding q =
      nativeCriticalDepth (baconShorCode m b).encoding q := by
  let C := baconShorCode m b
  let pX := physicalXWord (fullXColumn (rows := m + 1) (0 : Fin (b + 1)))
  let pZ := physicalZWord (fullZRow (columns := b + 1) (0 : Fin (m + 1)))
  have hXweight : (pauliSupport pX).card = m+1 := fullXColumn_support_card 0
  have hZweight : (pauliSupport pZ).card = b+1 := baconPhysicalZRow_weight 0
  apply le_antisymm
  · rw [baconShor_nativeCriticalDepth hm hmb q hq]
    apply nativeExactDepth_le_criticalDepth_of_shell C (by positivity) q (m + 1) hq
      (by omega) pX pZ baconPhysicalEncoding_bareX (baconPhysicalEncoding_bareZ 0)
    · rw [hXweight]
      exact (Nat.succ_le_succ hmb).trans hshell
    · rw [hZweight]
      exact hshell
  · exact (le_max_left _ _).trans (max_nativeCriticalDepth_nativeDenseDepth_le_nativeExactDepth
      C.encoding q (by decide))

#print axioms baconShor_nativeCriticalDepth
#print axioms baconShor_nativeExactDepth_upper
#print axioms baconShor_equal_thresholds_of_shell

end

end CriticalDepth.FaultShorSaturation.BaconShor
