import CriticalDepthMathlib

/-!
# Multiplicative closure of the physical Pauli matrices

The single-site product table keeps track of the phase before taking
tensor products. A fourth-root reduction puts the result back into
the four phases used by the physical Pauli definition.
-/

namespace CriticalDepth.PauliGroup

open Manuscript Matrix
open scoped BigOperators

private def singleProduct : SinglePauli → SinglePauli → ℕ × SinglePauli
  | .I, b => (0, b)
  | a, .I => (0, a)
  | .X, .X | .Y, .Y | .Z, .Z => (0, .I)
  | .X, .Y => (1, .Z)
  | .Y, .Z => (1, .X)
  | .Z, .X => (1, .Y)
  | .Y, .X => (3, .Z)
  | .Z, .Y => (3, .X)
  | .X, .Z => (3, .Y)

private theorem singleProduct_matrix (a b : SinglePauli) :
    a.matrix * b.matrix =
      (Complex.I ^ (singleProduct a b).1) • (singleProduct a b).2.matrix := by
  cases a <;> cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [singleProduct, SinglePauli.matrix, Matrix.mul_apply, Fin.sum_univ_two,
      pow_succ, Complex.I_mul_I, Matrix.smul_apply, smul_eq_mul]

private theorem phase_reduce (r : ℕ) : Complex.I ^ (r % 4) = Complex.I ^ r := by
  have hI : Complex.I ^ 4 = 1 := by
    calc
      Complex.I ^ 4 = (Complex.I * Complex.I) * (Complex.I * Complex.I) := by ring
      _ = 1 := by simp [Complex.I_mul_I]
  calc
    Complex.I ^ (r % 4) = Complex.I ^ (r % 4) * (Complex.I ^ 4) ^ (r / 4) := by
      rw [hI, one_pow, mul_one]
    _ = Complex.I ^ (r % 4 + 4 * (r / 4)) := by rw [pow_add, pow_mul]
    _ = Complex.I ^ r := by rw [Nat.mod_add_div]

private theorem isPauli_pow_smul {n : ℕ} (r : ℕ) (p : Fin n → SinglePauli) :
    IsPauli ((Complex.I ^ r) • pauliMatrix 0 p) := by
  refine ⟨⟨r % 4, Nat.mod_lt _ (by decide)⟩, p, ?_⟩
  rw [pauliMatrix_eq_phase_smul ⟨r % 4, Nat.mod_lt _ (by decide)⟩ p]
  exact congrArg (fun z : ℂ => z • pauliMatrix 0 p) (phase_reduce r).symm

private theorem unphased_pauliMatrix_mul {n : ℕ} (p q : Fin n → SinglePauli) :
    pauliMatrix 0 p * pauliMatrix 0 q =
      (Complex.I ^ ∑ i, (singleProduct (p i) (q i)).1) •
        pauliMatrix 0 (fun i => (singleProduct (p i) (q i)).2) := by
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  simp_rw [singleProduct_matrix]
  rw [tensorEntries_smul, Finset.prod_pow_eq_pow_sum]

theorem isPauli_mul {n : ℕ} {A B : Operator (QubitBasis n)}
    (hA : IsPauli A) (hB : IsPauli B) : IsPauli (A * B) := by
  obtain ⟨a, p, rfl⟩ := hA
  obtain ⟨b, q, rfl⟩ := hB
  rw [pauliMatrix_eq_phase_smul a p, pauliMatrix_eq_phase_smul b q,
    Matrix.smul_mul, Matrix.mul_smul, unphased_pauliMatrix_mul,
    smul_smul, smul_smul, ← pow_add, ← pow_add]
  exact isPauli_pow_smul _ _

theorem isPauli_star {n : ℕ} {A : Operator (QubitBasis n)}
    (hA : IsPauli A) : IsPauli (star A) := by
  obtain ⟨a, p, rfl⟩ := hA
  have hI : star Complex.I = Complex.I ^ 3 := by
    norm_num [pow_succ, Complex.I_mul_I]
  rw [pauliMatrix_eq_phase_smul, star_smul, star_pow, hI, ← pow_mul,
    Matrix.star_eq_conjTranspose, unphased_pauliMatrix_selfAdjoint]
  exact isPauli_pow_smul _ _

theorem isPauli_one (n : ℕ) : IsPauli (1 : Operator (QubitBasis n)) := by
  refine ⟨0, fun _ => SinglePauli.I, ?_⟩
  rw [pauliMatrix_zero_eq_tensorEntries]
  exact (tensorEntries_one (R := ℂ) (α := fun _ : Fin n => Fin 2)).symm

/-- The physical Pauli subgroup of the matrix unitary group. -/
noncomputable def physicalPauliGroup (n : ℕ) :
    Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ) where
  carrier := {U | IsPauli U.val}
  one_mem' := isPauli_one n
  mul_mem' := fun hA hB => isPauli_mul hA hB
  inv_mem' := fun hA => isPauli_star hA

theorem physicalPauliGroup_mem_iff (n : ℕ) (U : Matrix.unitaryGroup (QubitBasis n) ℂ) :
    U ∈ physicalPauliGroup n ↔ IsPauli U.val := Iff.rfl

#print axioms physicalPauliGroup
#print axioms physicalPauliGroup_mem_iff

end CriticalDepth.PauliGroup
