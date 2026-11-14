import CSSFourierCharacterSums
import Q37CanonicalEncoding
import CliffordTWords
import FaultOnSiteSupport

/-!
# Tensor Hadamard on the ordered Q37 CSS basis
-/

open scoped BigOperators Kronecker Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.Manuscript20261114.CliffordT
open CriticalDepth.FaultShorSaturation CriticalDepth.FaultSupportPreserving

noncomputable section

open Classical

variable {n : ℕ}

local instance (H : Submodule CSSBit (CSSWord n)) : Fintype H := Fintype.ofFinite H

private def hScale : ℝ := Real.sqrt 2 / 2

private theorem hadamardMatrix_sign (a b : Fin 2) :
    hadamardMatrix a b = (hScale : ℂ) * (if a = 1 ∧ b = 1 then -1 else 1) := by
  fin_cases a <;> fin_cases b <;> simp [hadamardMatrix, smul_eq_mul] <;> rfl

def physicalHadamard (n : ℕ) : Operator (QubitBasis n) :=
  tensorEntries (fun _ : Fin n => hadamardMatrix)

theorem physicalHadamard_isUnitary (n : ℕ) : IsUnitary (physicalHadamard n) :=
  isUnitary_tensorEntries _ (fun _ => hadamardUnitary.property)

theorem physicalHadamard_selfAdjoint (n : ℕ) :
    (physicalHadamard n).conjTranspose = physicalHadamard n := by
  unfold physicalHadamard
  rw [← tensorEntries_conjTranspose]
  have h : hadamardMatrix.conjTranspose = hadamardMatrix := hadamardMatrix_selfAdjoint
  simp only [h]

private theorem physicalHadamard_apply (x y : QubitBasis n) :
    physicalHadamard n x y = (hScale : ℂ) ^ n *
      cssSign (dotProduct (binaryWordEquiv n x) (binaryWordEquiv n y)) := by
  classical
  have hi (a b : Fin 2) : hadamardMatrix a b =
      (hScale : ℂ) * cssSign (qubitBitEquiv a * qubitBitEquiv b) := by
    rw [hadamardMatrix_sign]
    fin_cases a <;> fin_cases b <;> simp [qubitBitEquiv, cssSign]
  unfold physicalHadamard tensorEntries
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [dotProduct, cssSign_sum]
  rfl

/-- Tensor Hadamard maps a CSS coset basis vector to its exact character
on the dual space. -/
theorem physicalHadamard_mul_orderedCSSEncoding
    (H J : Submodule CSSBit (CSSWord n)) (hHJ : H ≤ cssOrthogonal J)
    {k : CSSWord n} (hk : k ∈ cssOrthogonal J) (x : QubitBasis n) (b : Fin 2 × Fin 1) :
    (physicalHadamard n * orderedCSSEncoding H J hk) x b =
      if binaryWordEquiv n x ∈ cssOrthogonal H then
        ((hScale : ℂ) ^ n * cosetAmplitude H * (Fintype.card H : ℂ)) *
          cssSign (dotProduct (binaryWordEquiv n x) (logicalRepresentative J hk b).val)
      else 0 := by
  classical
  let r := logicalRepresentative J hk b
  let y := binaryWordEquiv n x
  rw [Matrix.mul_apply]
  simp_rw [physicalHadamard_apply]
  have hsummand (a : QubitBasis n) :
      (hScale : ℂ) ^ n * cssSign (dotProduct y (binaryWordEquiv n a)) *
        orderedCSSEncoding H J hk a b =
      ((hScale : ℂ) ^ n * cosetAmplitude H) *
        (if binaryWordEquiv n a ∈ cosetWords H J ((insideChecks H J).mkQ r)
          then cssSign (dotProduct y (binaryWordEquiv n a)) else 0) := by
    change _ * cssCosetEncoding H J (binaryWordEquiv n a) ((insideChecks H J).mkQ r) = _
    unfold cssCosetEncoding
    split <;> simp_all [mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_congr rfl (fun a _ => hsummand a), ← Finset.mul_sum]
  let f (z : CSSWord n) : ℂ :=
    if z ∈ cosetWords H J ((insideChecks H J).mkQ r) then cssSign (dotProduct y z) else 0
  have hsum : (∑ a : QubitBasis n, f (binaryWordEquiv n a)) = ∑ z : CSSWord n, f z :=
    (binaryWordEquiv n).sum_comp f
  have hsum' : (∑ a : QubitBasis n, if binaryWordEquiv n a ∈ cosetWords H J ((insideChecks H J).mkQ r)
      then cssSign (dotProduct y (binaryWordEquiv n a)) else 0) =
      ∑ z : CSSWord n, if z ∈ cosetWords H J ((insideChecks H J).mkQ r) then cssSign (dotProduct y z) else 0 := hsum
  rw [hsum']
  rw [← Finset.sum_filter]
  have he : (Finset.univ.filter fun (z : CSSWord n) =>
      z ∈ cosetWords H J ((insideChecks H J).mkQ r)) =
      cosetWords H J ((insideChecks H J).mkQ r) := by
    ext z
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [he, sum_cssSign_dot_coset H J hHJ r y]
  by_cases hy : y ∈ cssOrthogonal H
  · change _ = if y ∈ cssOrthogonal H then _ else _
    rw [ite_eq_left hy, ite_eq_left hy, ← mul_assoc]
  · change _ = if y ∈ cssOrthogonal H then _ else _
    rw [if_neg hy, if_neg hy, mul_zero]

private theorem q37_phase_amplitude :
    (hScale : ℂ) ^ 37 * cosetAmplitude q37XChecks * (Fintype.card q37XChecks : ℂ) =
      (hScale : ℂ) * cosetAmplitude q37ZChecks := by
  have hx : Fintype.card q37XChecks = 2 ^ 18 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := CSSBit),
      q37XChecks_finrank, Nat.card_eq_fintype_card, ZMod.card]
  have hz : Fintype.card q37ZChecks = 2 ^ 18 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := CSSBit),
      q37ZChecks_finrank, Nat.card_eq_fintype_card, ZMod.card]
  have hAmp : cosetAmplitude q37XChecks = cosetAmplitude q37ZChecks := by
    simp [cosetAmplitude, hx, hz]
  have hs : (hScale : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    have hr : hScale ^ 2 = 1 / 2 := by
      have hr' := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      unfold hScale
      nlinarith
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    simpa using hc
  calc
    _ = (((hScale : ℂ) ^ 2) ^ 18 * (hScale : ℂ)) *
      cosetAmplitude q37ZChecks * (Fintype.card q37XChecks : ℂ) := by
      rw [← pow_mul, ← pow_succ, show 2 * 18 + 1 = 37 by decide, hAmp]
    _ = _ := by
      rw [hs, hx]
      norm_num
      ring

private theorem q37_fourier_bit_sign (z : Q37Word) (b : Fin 2 × Fin 1)
    (d : Fin 2 × Fin 1) (hx : z ∈ cssOrthogonal q37XChecks)
    (hc : (insideChecks q37ZChecks q37XChecks).mkQ
      (⟨z, hx⟩ : cssOrthogonal q37XChecks) =
        logicalCoset q37ZChecks q37XChecks q37LogicalZ_in_dual d) :
    cssSign (dotProduct z (logicalRepresentative q37ZChecks q37LogicalX_in_dual b).val) =
      if b.1 = 1 ∧ d.1 = 1 then -1 else 1 := by
  let r := logicalRepresentative q37XChecks q37LogicalZ_in_dual d
  have hq : (insideChecks q37ZChecks q37XChecks).mkQ
       ((⟨z, hx⟩ : cssOrthogonal q37XChecks) - r) = 0 := by
    rw [map_sub, hc]
    change ((insideChecks q37ZChecks q37XChecks).mkQ r) - ((insideChecks q37ZChecks q37XChecks).mkQ r) = 0
    exact sub_self _
  have hZR : z - r.val ∈ q37ZChecks :=
    (Submodule.Quotient.mk_eq_zero (insideChecks q37ZChecks q37XChecks)).mp hq
  have hZR' := q37LogicalX_in_dual (z - r.val) hZR
  have hDiff : dotProduct q37LogicalX z = dotProduct q37LogicalX r.val := by
    simpa [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hZR'
  have h01 (i : Fin 2) : i = 0 ∨ i = 1 := by decide +revert
  rcases h01 b.1 with hb | hb <;> rcases h01 d.1 with hd | hd
  · simp [logicalRepresentative, hb, hd, cssSign]
  · simp [logicalRepresentative, hb, hd, cssSign]
  · have hbRep : (logicalRepresentative q37ZChecks q37LogicalX_in_dual b).val = q37LogicalX := by
      simp [logicalRepresentative, hb]
    rw [hbRep, show dotProduct z q37LogicalX = 0 by
      rw [dotProduct_comm, hDiff, show r.val = 0 by simp [r, logicalRepresentative, hd],
        dotProduct_zero]]
    simp [logicalRepresentative, hb, hd, cssSign]
  · have hbRep : (logicalRepresentative q37ZChecks q37LogicalX_in_dual b).val = q37LogicalX := by
      simp [logicalRepresentative, hb]
    rw [hbRep, show dotProduct z q37LogicalX = 1 by
      rw [dotProduct_comm, hDiff, show r.val = q37LogicalZ by simp [r, logicalRepresentative, hd],
        q37Logical_dot]]
    simp [logicalRepresentative, hb, hd, cssSign]

private theorem orderedCSSEncoding_eq_amplitude_or_zero (H J : Submodule CSSBit (CSSWord n))
    {k : CSSWord n} (hk : k ∈ cssOrthogonal J) (x : QubitBasis n) (c : Fin 2 × Fin 1) :
    orderedCSSEncoding H J hk x c =
      if binaryWordEquiv n x ∈ cosetWords H J (logicalCoset H J hk c) then cosetAmplitude H else 0 := by
  classical
  rfl

/-- Determine each entry using a chosen coset of an orthogonal word,
with no expansion of the quotient or check matrices. -/
private theorem orderedCSSEncoding_apply_of_class (H J : Submodule CSSBit (CSSWord n))
    {k : CSSWord n} (hk : k ∈ cssOrthogonal J) (hn : k ∉ H) (hkDim : cssLogicalQubits H J = 1)
    (x : QubitBasis n) (d : Fin 2 × Fin 1) (hy : binaryWordEquiv n x ∈ cssOrthogonal J)
    (hd : (insideChecks H J).mkQ ⟨binaryWordEquiv n x, hy⟩ = logicalCoset H J hk d)
    (c : Fin 2 × Fin 1) :
    orderedCSSEncoding H J hk x c = if c = d then cosetAmplitude H else 0 := by
  classical
  rw [orderedCSSEncoding_eq_amplitude_or_zero]
  have hdmem : binaryWordEquiv n x ∈ cosetWords H J (logicalCoset H J hk d) :=
    (mem_cosetWords H J _ _).2 ⟨hy, hd⟩
  have he : binaryWordEquiv n x ∈ cosetWords H J (logicalCoset H J hk c) ↔ c = d := by
    constructor
    · intro hc
      apply (logicalCosetEquiv H J hk hn hkDim).injective
      exact cosetWords_unique H J _ _ _ hc hdmem
    · rintro rfl
      exact hdmem
  simp only [he]

/-- Nonorthogonal computational words vanish in each coset. -/
private theorem orderedCSSEncoding_apply_of_not_orthogonal (H J : Submodule CSSBit (CSSWord n))
    {k : CSSWord n} (hk : k ∈ cssOrthogonal J) (x : QubitBasis n)
    (hy : binaryWordEquiv n x ∉ cssOrthogonal J) (c : Fin 2 × Fin 1) :
    orderedCSSEncoding H J hk x c = 0 := by
  classical
  rw [orderedCSSEncoding_eq_amplitude_or_zero, if_neg]
  exact fun h => hy ((mem_cosetWords H J _ _).1 h).choose

set_option maxRecDepth 5000 in
/-- Physical Hadamard exchanges the two check-space encodings and applies
ordinary logical Hadamard in the registered logical basis. -/
theorem q37_physicalHadamard_transports_encoding :
    physicalHadamard 37 * q37CanonicalEncoding =
      q37DualEncoding * (hadamardMatrix ⊗ₖ (1 : Operator (Fin 1))) := by
  classical
  ext x b
  change (physicalHadamard 37 * orderedCSSEncoding q37XChecks q37ZChecks
    q37LogicalX_in_dual) x b = _
  rw [physicalHadamard_mul_orderedCSSEncoding _ _ q37ChecksCompatible]
  let y := binaryWordEquiv 37 x
  let e := logicalCosetEquiv q37ZChecks q37XChecks q37LogicalZ_in_dual
    q37LogicalZ_not_check q37SwappedLogicalQubits
  let A : Matrix (QubitBasis 37) (Fin 2 × Fin 1) ℂ := q37DualEncoding
  let z := cosetAmplitude q37ZChecks
  change (if y ∈ cssOrthogonal q37XChecks then _ else _) =
    (A * (hadamardMatrix ⊗ₖ (1 : Operator (Fin 1)))) x b
  by_cases hy : y ∈ cssOrthogonal q37XChecks
  · rw [ite_eq_left hy, q37_phase_amplitude]
    let d := e.symm ((insideChecks q37ZChecks q37XChecks).mkQ ⟨y, hy⟩)
    have hd : (insideChecks q37ZChecks q37XChecks).mkQ ⟨y, hy⟩ =
        logicalCoset q37ZChecks q37XChecks q37LogicalZ_in_dual d :=
      (e.apply_symm_apply _).symm
    have hRow (c : Fin 2 × Fin 1) : A x c = if c = d then z else 0 :=
      orderedCSSEncoding_apply_of_class q37ZChecks q37XChecks q37LogicalZ_in_dual
        q37LogicalZ_not_check q37SwappedLogicalQubits x d hy hd c
    have hPhase := q37_fourier_bit_sign y b d hy hd
    rw [hPhase, Matrix.mul_apply]
    simp_rw [hRow]
    rw [Finset.sum_eq_single d]
    · rw [ite_eq_left rfl, Matrix.kronecker_apply]
      have hs : (1 : Operator (Fin 1)) d.2 b.2 = 1 := by
        rw [Subsingleton.elim b.2 d.2, Matrix.one_apply_eq]
      rw [hs, mul_one, hadamardMatrix_sign]
      have hc : (b.1 = 1 ∧ d.1 = 1) ↔ (d.1 = 1 ∧ b.1 = 1) := and_comm
      simp only [hc]
      ring
    · intro c _ hc
      rw [ite_eq_right hc, zero_mul]
    · simp
  · rw [ite_eq_right hy, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro c _
    have hz : A x c = 0 :=
      orderedCSSEncoding_apply_of_not_orthogonal q37ZChecks q37XChecks
        q37LogicalZ_in_dual x hy c
    rw [hz, zero_mul]

theorem physicalHadamard_sq (n : ℕ) :
    physicalHadamard n * physicalHadamard n = 1 := by
  have h := (physicalHadamard_isUnitary n).1
  change (physicalHadamard n).conjTranspose * physicalHadamard n = 1 at h
  rwa [physicalHadamard_selfAdjoint] at h

#print axioms physicalHadamard_mul_orderedCSSEncoding
#print axioms q37_physicalHadamard_transports_encoding

end

end CriticalDepth.Q37BinaryData
