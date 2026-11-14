import CSSCodeStabilizer

/-!
# Every CSS stabilizer is an exact positive-ordered XZ product
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open scoped BigOperators

variable {n : ℕ}

private theorem cssBit_two (x y : CSSBit) :
    (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1) := by decide +revert

private theorem cssBit_add_self (x : CSSBit) : x + x = 0 := by decide +revert

private theorem pureX_add (a b : CSSWord n) :
    pauliMatrix 0 (cssXWord a) * pauliMatrix 0 (cssXWord b) =
      pauliMatrix 0 (cssXWord (a + b)) := by
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  congr 1
  funext i
  have h (w t : CSSBit) :
      (if w = 0 then SinglePauli.I else .X).matrix *
        (if t = 0 then SinglePauli.I else .X).matrix =
      (if w + t = 0 then SinglePauli.I else .X).matrix := by
    obtain ⟨hw, ht⟩ := cssBit_two w t
    rcases hw with (rfl | rfl) <;> rcases ht with (rfl | rfl) <;>
      simp only [zero_add, add_zero, cssBit_add_self, ite_true, one_ne_zero, ite_false]
    all_goals first | exact singlePauli_sq _ | simp [SinglePauli.matrix]
  exact h (a i) (b i)

theorem cssPureZ_add (a b : CSSWord n) :
    pauliMatrix 0 (cssZWord a) * pauliMatrix 0 (cssZWord b) =
      pauliMatrix 0 (cssZWord (a + b)) := by
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  congr 1
  funext i
  have h (w t : CSSBit) :
      (if w = 0 then SinglePauli.I else .Z).matrix *
        (if t = 0 then SinglePauli.I else .Z).matrix =
      (if w + t = 0 then SinglePauli.I else .Z).matrix := by
    obtain ⟨hw, ht⟩ := cssBit_two w t
    rcases hw with (rfl | rfl) <;> rcases ht with (rfl | rfl) <;>
      simp only [zero_add, add_zero, cssBit_add_self, ite_true, one_ne_zero, ite_false]
    all_goals first | exact singlePauli_sq _ | simp [SinglePauli.matrix]
  exact h (a i) (b i)

private theorem pureXZ_commutes (a b : CSSWord n) (hab : dotProduct a b = 0) :
    pauliMatrix 0 (cssXWord a) * pauliMatrix 0 (cssZWord b) =
      pauliMatrix 0 (cssZWord b) * pauliMatrix 0 (cssXWord a) := by
  have hs : (∏ i, (cssXWord a i).commutationSign (cssZWord b i)) = 1 := by
    calc
      _ = ∏ i, cssSign (a i * b i) := by
        apply Finset.prod_congr rfl
        intro i _
        change (if a i = 0 then SinglePauli.I else .X).commutationSign
          (if b i = 0 then SinglePauli.I else .Z) = cssSign (a i * b i)
        generalize a i = w
        generalize b i = t
        obtain ⟨hw, ht⟩ := cssBit_two w t
        rcases hw with (rfl | rfl) <;> rcases ht with (rfl | rfl) <;>
          simp [SinglePauli.commutationSign, cssSign]
      _ = cssSign (dotProduct a b) := by rw [dotProduct, cssSign_sum]
      _ = 1 := by simp [cssSign, hab]
  simpa only [hs, one_smul] using unphased_pauliMatrix_commutation (cssXWord a) (cssZWord b)

private theorem pureX_zero : pauliMatrix 0 (cssXWord (0 : CSSWord n)) = 1 := by
  rw [pauliMatrix_zero_eq_tensorEntries]
  change tensorEntries (fun i : Fin n => (cssXWord 0 i).matrix) = 1
  simp [cssXWord, SinglePauli.matrix, tensorEntries_one]

theorem cssPureZ_zero : pauliMatrix 0 (cssZWord (0 : CSSWord n)) = 1 := by
  rw [pauliMatrix_zero_eq_tensorEntries]
  change tensorEntries (fun i : Fin n => (cssZWord 0 i).matrix) = 1
  simp [cssZWord, SinglePauli.matrix, tensorEntries_one]

noncomputable section

variable (H J : Submodule CSSBit (CSSWord n)) (hHJ : H ≤ cssOrthogonal J)

private def xzSubgroup : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ) where
  carrier := {U | ∃ a ∈ H, ∃ b ∈ J,
    U.val = pauliMatrix 0 (cssXWord a) * pauliMatrix 0 (cssZWord b)}
  one_mem' := by
    exact ⟨0, H.zero_mem, 0, J.zero_mem, by rw [pureX_zero, cssPureZ_zero, Matrix.mul_one]; rfl⟩
  mul_mem' := by
    rintro U V ⟨a, ha, b, hb, hU⟩ ⟨a', ha', b', hb', hV⟩
    refine ⟨a + a', H.add_mem ha ha', b + b', J.add_mem hb hb', ?_⟩
    have hc : pauliMatrix 0 (cssXWord a') * pauliMatrix 0 (cssZWord b) =
        pauliMatrix 0 (cssZWord b) * pauliMatrix 0 (cssXWord a') :=
      pureXZ_commutes a' b (hHJ ha' b hb)
    change U.val * V.val = _
    rw [hU, hV, ← pureX_add, ← cssPureZ_add]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (pauliMatrix 0 (cssZWord b)), ← hc, Matrix.mul_assoc]
  inv_mem' := by
    rintro U ⟨a, ha, b, hb, hU⟩
    refine ⟨a, ha, b, hb, ?_⟩
    have hc := pureXZ_commutes a b (hHJ ha b hb)
    change star U.val = _
    rw [hU, star_mul, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      unphased_pauliMatrix_selfAdjoint, unphased_pauliMatrix_selfAdjoint, hc]

include hHJ in
theorem cssStabilizer_mem_iff_XZ (U : Matrix.unitaryGroup (QubitBasis n) ℂ) :
    U ∈ cssStabilizer H J ↔ ∃ a ∈ H, ∃ b ∈ J,
      U.val = pauliMatrix 0 (cssXWord a) * pauliMatrix 0 (cssZWord b) := by
  constructor
  · have hle : cssStabilizer H J ≤ xzSubgroup H J hHJ := by
      unfold cssStabilizer
      apply (Subgroup.closure_le (xzSubgroup H J hHJ)).mpr
      intro G hG
      rcases hG with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · refine ⟨a, ha, 0, J.zero_mem, ?_⟩
        rw [cssPureZ_zero, Matrix.mul_one]
        rfl
      · refine ⟨0, H.zero_mem, b, hb, ?_⟩
        rw [pureX_zero, Matrix.one_mul]
        rfl
    exact fun hU => hle hU
  · rintro ⟨a, ha, b, hb, hU⟩
    obtain ⟨X, hX, heX⟩ := exists_cssStabilizer_X H J a ha
    obtain ⟨Z, hZ, heZ⟩ := exists_cssStabilizer_Z H J b hb
    have h : U = X * Z := by
      apply Subtype.ext
      change U.val = X.val * Z.val
      rw [hU, heX, heZ]
    rw [h]
    exact (cssStabilizer H J).mul_mem hX hZ

#print axioms cssStabilizer_mem_iff_XZ

end

end CriticalDepth.Manuscript20261114.CSSCode
