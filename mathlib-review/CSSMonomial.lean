import CriticalDepthMathlib

/-!
# Monomial form from diagonal rank-one conjugates

The final step of the CSS monomial argument uses only finite unitary matrix
algebra. Preservation of the diagonal algebra implies the hypothesis.
-/

namespace CriticalDepth.CSSMonomial

open CriticalDepth.Manuscript Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem column_conj_matrixUnit
    (U : Operator ι) (j x y : ι) :
    (U * (Matrix.single j j (1 : ℂ) : Operator ι) * U.conjTranspose) x y = U x j * star (U y j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.single_mul_apply_same, one_mul]
    rfl
  · intro k _ hk
    rw [Matrix.single_mul_apply_of_ne (1 : ℂ) _ _ _ _ hk, mul_zero]
  · simp

theorem exists_monomial_of_diagonal_conjugates
    (U : Operator ι) (hu : IsUnitary U)
    (hdiag : ∀ j x y : ι, x ≠ y →
      (U * (Matrix.single j j (1 : ℂ) : Operator ι) * U.conjTranspose) x y = 0) :
    ∃ (f : Equiv.Perm ι) (phase : ι → ℂ),
      (∀ j, star (phase j) * phase j = 1) ∧
      ∀ x j, U x j = if x = f j then phase j else 0 := by
  classical
  have huEntry (i j : ι) :
      (∑ x, star (U x i) * U x j) = (1 : Operator ι) i j := by
    exact congrFun (congrFun hu.1 i) j
  have hnotzero (j : ι) : ∃ x, U x j ≠ 0 := by
    by_contra! hn
    have := huEntry j j
    simp [hn] at this
  choose f hf using hnotzero
  have hsupp (j x : ι) (hx : x ≠ f j) : U x j = 0 := by
    have h := hdiag j x (f j) hx
    rw [column_conj_matrixUnit] at h
    exact (mul_eq_zero.mp h).resolve_right (by simpa using hf j)
  have hsum (i j : ι) :
      (∑ x, star (U x i) * U x j) = star (U (f j) i) * U (f j) j := by
    apply Finset.sum_eq_single (f j)
    · intro x _ hx
      rw [hsupp j x hx, mul_zero]
    · simp
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h := huEntry i j
    rw [hsum, Matrix.one_apply_ne hne, ← hij] at h
    have hneJ : U (f i) j ≠ 0 := hij.symm ▸ hf j
    exact (mul_ne_zero (by simpa using hf i) hneJ) h
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hinj)
  refine ⟨e, fun j => U (f j) j, ?_, ?_⟩
  · intro j
    have h := huEntry j j
    rwa [hsum, Matrix.one_apply_eq] at h
  · intro x j
    change U x j = if x = f j then U (f j) j else 0
    by_cases hx : x = f j
    · simp [hx]
    · simpa [hx] using hsupp j x hx

#print axioms exists_monomial_of_diagonal_conjugates

end CriticalDepth.CSSMonomial