import CSSZConjugation
import CSSPauliRestriction
import CSSPermutationRigidity

/-!
# Diagonality of short operators commuting with the CSS Z checks
-/

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114.CSSZConjugation

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCheckSpaces
open CriticalDepth.FaultStabilizerTrace CriticalDepth.Manuscript20261114.CSSPauliRestriction Matrix

variable {n : ℕ}

/-- The X mask records the X and Y positions of an unphased Pauli word. -/
def xMask (p : Fin n → SinglePauli) : BinaryWord (Fin n) :=
  fun i => if p i = .X ∨ p i = .Y then 1 else 0

/-- The unphased tensor Z matrix indexed by a binary mask. -/
def zCheck (v : BinaryWord (Fin n)) : Operator (QubitBasis n) :=
  pauliMatrix 0 (fun i => if v i = 0 then .I else .Z)

private def checkSign (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

private theorem bit_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  decide +revert

private theorem checkSign_add (a b : ZMod 2) :
    checkSign (a + b) = checkSign a * checkSign b := by
  rcases bit_eq_zero_or_one a with (rfl | rfl) <;>
    rcases bit_eq_zero_or_one b with (rfl | rfl) <;>
    simp [checkSign, show ((1 : ZMod 2) + 1) = 0 by decide]

private theorem checkSign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    checkSign (∑ i ∈ s, f i) = ∏ i ∈ s, checkSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [checkSign]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, checkSign_add, ih]

private theorem zCheck_commutation (v : BinaryWord (Fin n)) (p : Fin n → SinglePauli) :
    zCheck v * pauliMatrix 0 p =
      checkSign (dotProduct v (xMask p)) • (pauliMatrix 0 p * zCheck v) := by
  unfold zCheck
  rw [unphased_pauliMatrix_commutation]
  congr 1
  rw [dotProduct, checkSign_sum]
  apply Finset.prod_congr rfl
  intro i _
  rcases bit_eq_zero_or_one (v i) with h | h <;> cases hp : p i <;>
    simp [h, hp, xMask, checkSign, SinglePauli.commutationSign]

private theorem zCheck_sq (v : BinaryWord (Fin n)) : zCheck v * zCheck v = 1 :=
  unphased_pauliMatrix_sq _

private theorem pauli_word_diagonal_of_zero_xMask (p : Fin n → SinglePauli)
    (hp : xMask p = 0) (x y : QubitBasis n) (hxy : x ≠ y) :
    pauliMatrix 0 p x y = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  rw [pauliMatrix_zero_eq_tensorEntries]
  change (∏ j, (p j).matrix (x j) (y j)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hpi := congrFun hp i
  cases h : p i with
  | I => simp [SinglePauli.matrix, Matrix.one_apply_ne hi]
  | X => simp [xMask, h] at hpi
  | Y => simp [xMask, h] at hpi
  | Z =>
    have hz (a b : Fin 2) (hab : a ≠ b) : SinglePauli.Z.matrix a b = 0 := by
      fin_cases a <;> fin_cases b <;> simp_all [SinglePauli.matrix]
    exact h ▸ hz _ _ hi

private theorem xMask_extendLocalPauli_weight_le (A : Finset (Fin n))
    (p : A → SinglePauli) : wordWeight (xMask (extendLocalPauli A p)) ≤ A.card := by
  apply wordWeight_le_of_supported
  intro i hi
  simp [xMask, extendLocalPauli, hi]

private theorem pauli_coefficient_eq_of_trace (A : Finset (Fin n))
    (c : (A → SinglePauli) → ℂ) (p : A → SinglePauli) :
    (pauliMatrix 0 (extendLocalPauli A p) *
      (∑ q, c q • pauliMatrix 0 (extendLocalPauli A q))).trace =
        c p * (Fintype.card (QubitBasis n) : ℂ) := by
  classical
  rw [Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
  · rw [Matrix.mul_smul, Matrix.trace_smul, unphased_pauliMatrix_sq,
      Matrix.trace_one, smul_eq_mul]
  · intro q _ hqp
    have hne : extendLocalPauli A p ≠ extendLocalPauli A q := by
      intro h
      apply hqp
      funext i
      have hi := congrFun h i.val
      simpa [extendLocalPauli, i.property] using hi.symm
    rw [Matrix.mul_smul, Matrix.trace_smul, pauli_mul_trace_eq_zero_of_ne hne, smul_zero]

private theorem coefficients_eq_of_expansions (A : Finset (Fin n))
    (c d : (A → SinglePauli) → ℂ)
    (hEq : (∑ p, c p • pauliMatrix 0 (extendLocalPauli A p)) =
      ∑ p, d p • pauliMatrix 0 (extendLocalPauli A p)) (p : A → SinglePauli) :
    c p = d p := by
  have h := congrArg (fun X => (pauliMatrix 0 (extendLocalPauli A p) * X).trace) hEq
  rw [pauli_coefficient_eq_of_trace, pauli_coefficient_eq_of_trace] at h
  exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h

/-- A supported operator commuting with every Z test has only diagonal
Pauli terms if every nonzero word passing those tests is longer than its
support. The tests' equations describe the CSS X-check space. -/
theorem diagonal_of_supported_commutes_zChecks
    {H : Submodule (ZMod 2) (BinaryWord (Fin n))} {D : ℕ}
    (tests : ShortOrthogonalityTests H D)
    (A : Finset (Fin n))
    (hDist : ∀ v ∈ H, v ≠ 0 → A.card < wordWeight v)
    (O : Operator (QubitBasis n)) (hA : SupportedOn O A)
    (hComm : ∀ v ∈ tests.tests, zCheck v * O = O * zCheck v)
    (x y : QubitBasis n) (hxy : x ≠ y) : O x y = 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_supported_pauli_expansion A O hA
  have hCoeff (v : BinaryWord (Fin n)) (hv : v ∈ tests.tests) (p : A → SinglePauli) :
      c p = c p * checkSign (dotProduct v (xMask (extendLocalPauli A p))) := by
    have hConj : zCheck v * O * zCheck v = O := by
      rw [hComm v hv, Matrix.mul_assoc, zCheck_sq, Matrix.mul_one]
    let d : (A → SinglePauli) → ℂ := fun p =>
      c p * checkSign (dotProduct v (xMask (extendLocalPauli A p)))
    have he : (∑ p, d p • pauliMatrix 0 (extendLocalPauli A p)) =
        ∑ p, c p • pauliMatrix 0 (extendLocalPauli A p) := by
      rw [← hc]
      calc
        _ = zCheck v * (∑ p, c p • pauliMatrix 0 (extendLocalPauli A p)) * zCheck v := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          apply Finset.sum_congr rfl
          intro q _
          rw [Matrix.mul_smul, Matrix.smul_mul, zCheck_commutation, Matrix.smul_mul,
            Matrix.mul_assoc, zCheck_sq, Matrix.mul_one, smul_smul]
        _ = O := by rwa [← hc]
    exact (coefficients_eq_of_expansions A d c he p).symm
  have hZero (p : A → SinglePauli) (hp : c p ≠ 0) :
      xMask (extendLocalPauli A p) = 0 := by
    let v := xMask (extendLocalPauli A p)
    have hv : v ∈ H := (tests.characterize v).mpr (by
      intro w hw
      have hsign := (mul_eq_left₀ hp).mp (hCoeff w hw p).symm
      change checkSign (dotProduct w v) = 1 at hsign
      by_contra hne
      rw [checkSign, ite_eq_right hne] at hsign
      norm_num at hsign)
    by_contra hne
    exact (not_lt_of_ge (xMask_extendLocalPauli_weight_le A p)) (hDist v hv hne)
  rw [hc, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : c p = 0
  · simp [hp]
  · rw [Matrix.smul_apply, pauli_word_diagonal_of_zero_xMask _ (hZero p hp) x y hxy, smul_zero]

#print axioms diagonal_of_supported_commutes_zChecks

end CriticalDepth.Manuscript20261114.CSSZConjugation
