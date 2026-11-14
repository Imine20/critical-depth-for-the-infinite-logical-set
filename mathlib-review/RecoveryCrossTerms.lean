import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.BigOperators

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114

/-- The matrix part of necessity in the Knill–Laflamme theorem. For a
trace-preserving recovery whose recovered branches act as scalars, the
overlap of two encoded errors is scalar. -/
theorem crossTerm_scalar_of_recoveryKraus {I P L : Type*}
    [Fintype I] [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
    (A B : Matrix P L ℂ) (R : I → Matrix L P ℂ)
    (a b : I → ℂ) (hTP : (∑ i, (R i).conjTranspose * R i) = 1)
    (hA : ∀ i, R i * A = a i • (1 : Matrix L L ℂ))
    (hB : ∀ i, R i * B = b i • (1 : Matrix L L ℂ)) :
    A.conjTranspose * B = (∑ i, star (a i) * b i) • (1 : Matrix L L ℂ) := by
  classical
  calc
    A.conjTranspose * B = A.conjTranspose * (∑ i, (R i).conjTranspose * R i) * B := by
      rw [hTP, Matrix.mul_one]
    _ = ∑ i, (R i * A).conjTranspose * (R i * B) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ∑ i, (star (a i) * b i) • (1 : Matrix L L ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hA, hB]
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, smul_smul]
      rw [mul_comm]
    _ = (∑ i, star (a i) * b i) • (1 : Matrix L L ℂ) := by rw [Finset.sum_smul]

#print axioms crossTerm_scalar_of_recoveryKraus

end CriticalDepth.Manuscript20261114
