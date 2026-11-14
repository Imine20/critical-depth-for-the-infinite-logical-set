import CSSCodePauliMasks
import CSSCodeStabilizerElements
import CSSPhysicalMonomial

/-!
# The CSS stabilizer and its short Pauli centralizer
-/

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCheckSpaces
open CriticalDepth.Manuscript20261114.CSSZConjugation

variable {n : ℕ} {H J : Submodule CSSBit (CSSWord n)}

private theorem commutationSign_eq_one_of_commutes
    (A B : Operator (QubitBasis n)) (hAsq : A * A = 1) (hBsq : B * B = 1)
    (s : CSSBit) (hComm : A * B = B * A)
    (hSign : A * B = cssSign s • (B * A)) : s = 0 := by
  by_contra hn
  rw [cssSign, ite_eq_right hn, neg_one_smul, hComm] at hSign
  have h := congrArg (fun M : Operator (QubitBasis n) => M * (A * B)) hSign
  have hInv : (B * A) * (A * B) = 1 := by
    calc
      _ = B * (A * A) * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hAsq, Matrix.mul_one, hBsq]
  rw [Matrix.neg_mul, hInv] at h
  have he := congrArg (fun M : Operator (QubitBasis n) => M 0 0) h
  norm_num at he

/-- Centralizing the physical CSS stabilizer means that the two Pauli
masks are orthogonal to the opposite check spaces. -/
theorem css_masks_mem_orthogonal_of_commutes_stabilizer
    (p : Fin n → SinglePauli)
    (hComm : ∀ U ∈ cssStabilizer H J,
      (U : Operator (QubitBasis n)) * pauliMatrix 0 p =
        pauliMatrix 0 p * (U : Operator (QubitBasis n))) :
    cssMaskX p ∈ cssOrthogonal J ∧ cssMaskZ p ∈ cssOrthogonal H := by
  constructor
  · intro b hb
    obtain ⟨U, hU, hZ⟩ := exists_cssStabilizer_Z H J b hb
    have hc := hComm U hU
    rw [hZ] at hc
    exact commutationSign_eq_one_of_commutes _ _ (unphased_pauliMatrix_sq _)
      (unphased_pauliMatrix_sq _) _ hc (cssZ_commutation b p)
  · intro a ha
    obtain ⟨U, hU, hX⟩ := exists_cssStabilizer_X H J a ha
    have hc := hComm U hU
    rw [hX] at hc
    exact commutationSign_eq_one_of_commutes _ _ (unphased_pauliMatrix_sq _)
      (unphased_pauliMatrix_sq _) _ hc (cssX_commutation a p)

private theorem pauli_eq_cssZWord_of_zero_maskX (p : Fin n → SinglePauli)
    (hp : cssMaskX p = 0) :
    pauliMatrix 0 p = pauliMatrix 0 (cssZWord (cssMaskZ p)) := by
  congr 1
  funext i
  have hxi : cssMaskX p i = 0 := congrFun hp i
  cases h : p i
  · have hz : cssMaskZ p i = 0 := by unfold cssMaskZ; rw [h]; rfl
    simp [cssZWord, hz, h]
  · exfalso
    have hx : cssMaskX p i = 1 := by unfold cssMaskX; rw [h]; rfl
    exact one_ne_zero (hx.symm.trans hxi)
  · exfalso
    have hx : cssMaskX p i = 1 := by unfold cssMaskX; rw [h]; rfl
    exact one_ne_zero (hx.symm.trans hxi)
  · have hz : cssMaskZ p i = 1 := by unfold cssMaskZ; rw [h]; rfl
    simp [cssZWord, hz, h]

private theorem extendLocalPauli_card_le (A : Finset (Fin n)) (p : A → SinglePauli) :
    (pauliSupport (extendLocalPauli A p)).card ≤ A.card := by
  apply Finset.card_le_card
  apply pauliSupport_subset_of_outside_identity
  intro i hi
  simp [extendLocalPauli, hi]

/-- The short physical CSS centralizer contains only Z checks of the
orthogonal X space if every nonzero X mask in the dual of J is longer. -/
theorem css_local_centralizer_eq_zCheck {B : ℕ}
    (hJ : ∀ b ∈ cssOrthogonal J, b ≠ 0 → B < wordWeight b)
    (A : Finset (Fin n)) (hA : A.card ≤ B) (p : A → SinglePauli)
    (hComm : ∀ U ∈ cssStabilizer H J,
      (U : Operator (QubitBasis n)) * pauliMatrix 0 (extendLocalPauli A p) =
        pauliMatrix 0 (extendLocalPauli A p) * (U : Operator (QubitBasis n))) :
    ∃ v ∈ cssOrthogonal H, pauliMatrix 0 (extendLocalPauli A p) = zCheck v := by
  let P := extendLocalPauli A p
  obtain ⟨hx, hz⟩ := css_masks_mem_orthogonal_of_commutes_stabilizer P hComm
  have hx0 : cssMaskX P = 0 := by
    by_contra hne
    exact (not_lt_of_ge ((cssMaskX_weight_le P).trans ((extendLocalPauli_card_le A p).trans hA)))
      (hJ _ hx hne)
  exact ⟨cssMaskZ P, hz, pauli_eq_cssZWord_of_zero_maskX P hx0⟩

private theorem cssXWord_commutes_cssXWord (a b : CSSWord n) :
    pauliMatrix 0 (cssXWord a) * pauliMatrix 0 (cssXWord b) =
      pauliMatrix 0 (cssXWord b) * pauliMatrix 0 (cssXWord a) := by
  have h : cssMaskZ (cssXWord b) = 0 := by
    funext i
    by_cases hi : b i = 0 <;> simp [cssMaskZ, cssXWord, hi] <;> rfl
  rw [cssX_commutation, h, zero_dotProduct, cssSign, ite_eq_left rfl, one_smul]

private theorem cssZWord_commutes_cssZWord (a b : CSSWord n) :
    pauliMatrix 0 (cssZWord a) * pauliMatrix 0 (cssZWord b) =
      pauliMatrix 0 (cssZWord b) * pauliMatrix 0 (cssZWord a) := by
  have h : cssMaskX (cssZWord b) = 0 := by
    funext i
    by_cases hi : b i = 0 <;> simp [cssMaskX, cssZWord, hi] <;> rfl
  rw [cssZ_commutation, h, zero_dotProduct, cssSign, ite_eq_left rfl, one_smul]

private theorem cssZWord_single (i : Fin n) :
    cssZWord (Pi.single i (1 : CSSBit)) = singleSitePauli i .Z := by
  funext j
  by_cases h : j = i
  · subst j
    simp [cssZWord, singleSitePauli]
  · simp [cssZWord, singleSitePauli, Pi.single_eq_of_ne h, h]

private theorem cssXWord_single (i : Fin n) :
    cssXWord (Pi.single i (1 : CSSBit)) = singleSitePauli i .X := by
  funext j
  by_cases h : j = i
  · subst j
    simp [cssXWord, singleSitePauli]
  · simp [cssXWord, singleSitePauli, Pi.single_eq_of_ne h, h]

private theorem cssMaskX_cssXWord (a : CSSWord n) : cssMaskX (cssXWord a) = a := by
  funext i
  have hi : a i = 0 ∨ a i = 1 := by
    generalize a i = b
    decide +revert
  rcases hi with hi | hi <;> simp only [cssMaskX, cssXWord, hi] <;> rfl

private theorem cssMaskZ_cssZWord (a : CSSWord n) : cssMaskZ (cssZWord a) = a := by
  funext i
  have hi : a i = 0 ∨ a i = 1 := by
    generalize a i = b
    decide +revert
  rcases hi with hi | hi <;> simp only [cssMaskZ, cssZWord, hi] <;> rfl

/-- If a pure XZ word is supported on A, both masks vanish away from A. -/
theorem css_masks_supported_of_xz_supported
    (a b : CSSWord n) (A : Finset (Fin n))
    (hSupp : SupportedOn (pauliMatrix 0 (cssXWord a) * pauliMatrix 0 (cssZWord b)) A) :
    (∀ i ∉ A, a i = 0) ∧ (∀ i ∉ A, b i = 0) := by
  constructor
  · intro i hi
    let z : CSSWord n := Pi.single i 1
    let Z := pauliMatrix 0 (cssZWord z)
    let X := pauliMatrix 0 (cssXWord a)
    let Y := pauliMatrix 0 (cssZWord b)
    have hZ : SupportedOn Z {i} := by
      change SupportedOn (pauliMatrix 0 (cssZWord z)) {i}
      rw [cssZWord_single]
      exact singleSitePauli_supportedOn _ i (Finset.mem_singleton_self i) .Z
    have hdis : Disjoint ({i} : Finset (Fin n)) A := by simpa using hi
    have hComm : Z * (X * Y) = X * Y * Z := hZ.commute hSupp hdis
    have hYZ : Y * Z = Z * Y := cssZWord_commutes_cssZWord _ _
    have hZX : Z * X = X * Z := by
      rw [Matrix.mul_assoc, hYZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc] at hComm
      have h := congrArg (fun M : Operator (QubitBasis n) => M * Y) hComm
      simpa only [Matrix.mul_assoc _ Y Y, unphased_pauliMatrix_sq, Matrix.mul_one, Y] using h
    have h := commutationSign_eq_one_of_commutes Z X (unphased_pauliMatrix_sq _)
      (unphased_pauliMatrix_sq _) _ hZX (cssZ_commutation z (cssXWord a))
    simpa only [cssMaskX_cssXWord, z, dotProduct_single_one] using h
  · intro i hi
    let x : CSSWord n := Pi.single i 1
    let X := pauliMatrix 0 (cssXWord x)
    let Y := pauliMatrix 0 (cssXWord a)
    let Z := pauliMatrix 0 (cssZWord b)
    have hX : SupportedOn X {i} := by
      change SupportedOn (pauliMatrix 0 (cssXWord x)) {i}
      rw [cssXWord_single]
      exact singleSitePauli_supportedOn _ i (Finset.mem_singleton_self i) .X
    have hdis : Disjoint ({i} : Finset (Fin n)) A := by simpa using hi
    have hComm : X * (Y * Z) = Y * Z * X := hX.commute hSupp hdis
    have hXY : X * Y = Y * X := cssXWord_commutes_cssXWord _ _
    rw [← Matrix.mul_assoc, hXY, Matrix.mul_assoc,
      Matrix.mul_assoc Y] at hComm
    have h := congrArg (fun M : Operator (QubitBasis n) => Y * M) hComm
    have hYsq : Y * Y = 1 := unphased_pauliMatrix_sq _
    have hXZ : X * Z = Z * X := by
      simpa only [← Matrix.mul_assoc Y Y, hYsq, Matrix.one_mul] using h
    have h := commutationSign_eq_one_of_commutes X Z (unphased_pauliMatrix_sq _)
      (unphased_pauliMatrix_sq _) _ hXZ (cssX_commutation x (cssZWord b))
    simpa only [cssMaskZ_cssZWord, x, dotProduct_single_one] using h

/-- If the two check spaces have no short nonzero word, a physically short
stabilizer matrix on the code can only be the identity. -/
theorem css_no_short_stabilizer (hHJ : H ≤ cssOrthogonal J) {B : ℕ}
    (hH : ∀ a ∈ H, a ≠ 0 → B < wordWeight a)
    (hJ : ∀ b ∈ J, b ≠ 0 → B < wordWeight b)
    (A : Finset (Fin n)) (hA : A.card ≤ B)
    (U : Matrix.unitaryGroup (QubitBasis n) ℂ) (hU : U ∈ cssStabilizer H J)
    (hSupp : SupportedOn U.val A) : U = 1 := by
  obtain ⟨a, ha, b, hb, hProd⟩ := (cssStabilizer_mem_iff_XZ H J hHJ U).mp hU
  have hSupp' := hSupp
  rw [hProd] at hSupp'
  obtain ⟨hsa, hsb⟩ := css_masks_supported_of_xz_supported a b A hSupp'
  have ha0 : a = 0 := by
    by_contra hn
    exact (not_lt_of_ge ((wordWeight_le_of_supported hsa).trans hA)) (hH a ha hn)
  have hb0 : b = 0 := by
    by_contra hn
    exact (not_lt_of_ge ((wordWeight_le_of_supported hsb).trans hA)) (hJ b hb hn)
  apply Subtype.ext
  change U.val = (1 : Operator (QubitBasis n))
  rw [hProd, ha0, hb0]
  have hX : pauliMatrix 0 (cssXWord (0 : CSSWord n)) = 1 := by
    rw [pauliMatrix_zero_eq_tensorEntries]
    simp [cssXWord, SinglePauli.matrix, tensorEntries_one]
  have hZ : pauliMatrix 0 (cssZWord (0 : CSSWord n)) = 1 := by
    rw [pauliMatrix_zero_eq_tensorEntries]
    simp [cssZWord, SinglePauli.matrix, tensorEntries_one]
  rw [hX, hZ, Matrix.one_mul]

#print axioms css_masks_mem_orthogonal_of_commutes_stabilizer
#print axioms css_local_centralizer_eq_zCheck
#print axioms css_no_short_stabilizer

end CriticalDepth.Manuscript20261114.CSSCode
