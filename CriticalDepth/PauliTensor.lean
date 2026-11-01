import CriticalDepth.ManuscriptStatements
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Concrete tensor matrices and Pauli strings

The tensor-entry definition uses the manuscript's full computational basis.
No qubit disappears when a factor is an identity. Hermitian and involution
claims below are restricted to unphased strings; arbitrary Pauli phases are
handled separately for unitarity and commutation.
-/

noncomputable section

namespace CriticalDepth

open Matrix
open scoped BigOperators

def tensorEntries {I : Type*} [Fintype I] {R : Type*} [CommMonoid R]
    {α β : I → Type*} (A : ∀ i, Matrix (α i) (β i) R) :
    Matrix ((i : I) → α i) ((i : I) → β i) R :=
  fun x y => ∏ i, A i (x i) (y i)

theorem tensorEntries_mul
    {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommSemiring R]
    {α β γ : I → Type*} [∀ i, Fintype (β i)]
    (A : ∀ i, Matrix (α i) (β i) R) (B : ∀ i, Matrix (β i) (γ i) R) :
    tensorEntries (fun i => A i * B i) = tensorEntries A * tensorEntries B := by
  classical
  ext x z
  simp only [tensorEntries, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem tensorEntries_one
    {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommSemiring R]
    {α : I → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] :
    tensorEntries (fun i => (1 : Matrix (α i) (α i) R)) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorEntries]
  · have hex : ∃ i, x i ≠ y i := by
      by_contra hn
      apply hxy
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have hzero : (∏ j, (1 : Matrix (α j) (α j) R) (x j) (y j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Matrix.one_apply, hi]
    simpa [tensorEntries, Matrix.one_apply, hxy] using hzero

theorem tensorEntries_smul
    {I : Type*} [Fintype I] {R : Type*} [CommSemiring R]
    {α β : I → Type*} (z : I → R) (A : ∀ i, Matrix (α i) (β i) R) :
    tensorEntries (fun i => z i • A i) = (∏ i, z i) • tensorEntries A := by
  ext x y
  simp [tensorEntries, Finset.prod_mul_distrib, smul_eq_mul]

theorem tensorEntries_conjTranspose
    {I : Type*} [Fintype I] {α β : I → Type*}
    (A : ∀ i, Matrix (α i) (β i) ℂ) :
    tensorEntries (fun i => (A i).conjTranspose) = (tensorEntries A).conjTranspose := by
  ext x y
  simp [tensorEntries, Matrix.conjTranspose_apply]

theorem unitary_smul_of_phase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (U : Operator ι) (hz : star z * z = 1) (hU : IsUnitary U) :
    IsUnitary (z • U) := by
  have hz' : z * star z = 1 := by simpa [mul_comm] using hz
  constructor
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.1]
    change (z * star z) • (1 : Operator ι) = 1
    rw [hz', one_smul]
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.2]
    change (star z * z) • (1 : Operator ι) = 1
    rw [hz, one_smul]

theorem i_pow_unit_modulus (r : ℕ) :
    star (Complex.I ^ r) * Complex.I ^ r = 1 := by
  rw [star_pow, ← mul_pow]
  simp

theorem prod_signs_eq_one_or_neg_one
    {I : Type*} [Fintype I] (s : I → ℂ) (h : ∀ i, s i = 1 ∨ s i = -1) :
    (∏ i, s i) = 1 ∨ (∏ i, s i) = -1 := by
  classical
  have haux : ∀ t : Finset I,
      (∀ i ∈ t, s i = 1 ∨ s i = -1) → t.prod s = 1 ∨ t.prod s = -1 := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        intro ht
        have hsign := ht a (by simp)
        have htail := ih (fun i hi => ht i (by simp [hi]))
        simp only [Finset.prod_insert ha]
        rcases hsign with hs | hs <;> rcases htail with hh | hh <;> simp [hs, hh]
  exact haux Finset.univ (fun i _ => h i)

namespace Manuscript

theorem singlePauli_selfAdjoint (p : SinglePauli) : p.matrix.conjTranspose = p.matrix := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [SinglePauli.matrix, Matrix.conjTranspose_apply]

theorem singlePauli_sq (p : SinglePauli) : p.matrix * p.matrix = 1 := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [SinglePauli.matrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem singlePauli_isUnitary (p : SinglePauli) : IsUnitary p.matrix := by
  constructor
  · change p.matrix.conjTranspose * p.matrix = 1
    rw [singlePauli_selfAdjoint, singlePauli_sq]
  · change p.matrix * p.matrix.conjTranspose = 1
    rw [singlePauli_selfAdjoint, singlePauli_sq]

def SinglePauli.commutationSign (p q : SinglePauli) : ℂ :=
  if p = .I ∨ q = .I ∨ p = q then 1 else -1

theorem singlePauli_commutationSign_eq_one_or_neg_one (p q : SinglePauli) :
    p.commutationSign q = 1 ∨ p.commutationSign q = -1 := by
  unfold SinglePauli.commutationSign
  split_ifs <;> simp

theorem singlePauli_commutation (p q : SinglePauli) :
    p.matrix * q.matrix = p.commutationSign q • (q.matrix * p.matrix) := by
  cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [SinglePauli.matrix, SinglePauli.commutationSign, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I]

theorem pauliMatrix_zero_eq_tensorEntries {n : ℕ} (p : Fin n → SinglePauli) :
    pauliMatrix (0 : Fin 4) p = tensorEntries (fun i => (p i).matrix) := by
  ext x y
  simp [pauliMatrix, tensorEntries]

theorem unphased_pauliMatrix_selfAdjoint {n : ℕ} (p : Fin n → SinglePauli) :
    (pauliMatrix (0 : Fin 4) p).conjTranspose = pauliMatrix (0 : Fin 4) p := by
  simp only [pauliMatrix_zero_eq_tensorEntries]
  rw [← tensorEntries_conjTranspose]
  simp only [singlePauli_selfAdjoint]

theorem unphased_pauliMatrix_sq {n : ℕ} (p : Fin n → SinglePauli) :
    pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) p = 1 := by
  simp only [pauliMatrix_zero_eq_tensorEntries]
  rw [← tensorEntries_mul]
  simp only [singlePauli_sq, tensorEntries_one]

theorem unphased_pauliMatrix_isUnitary {n : ℕ} (p : Fin n → SinglePauli) :
    IsUnitary (pauliMatrix (0 : Fin 4) p) := by
  constructor
  · change (pauliMatrix (0 : Fin 4) p).conjTranspose * pauliMatrix (0 : Fin 4) p = 1
    rw [unphased_pauliMatrix_selfAdjoint, unphased_pauliMatrix_sq]
  · change pauliMatrix (0 : Fin 4) p * (pauliMatrix (0 : Fin 4) p).conjTranspose = 1
    rw [unphased_pauliMatrix_selfAdjoint, unphased_pauliMatrix_sq]

theorem pauliMatrix_eq_phase_smul {n : ℕ} (phase : Fin 4) (p : Fin n → SinglePauli) :
    pauliMatrix phase p = (Complex.I ^ phase.val) • pauliMatrix (0 : Fin 4) p := by
  ext x y
  simp [pauliMatrix, smul_eq_mul]

theorem pauliMatrix_isUnitary {n : ℕ} (phase : Fin 4) (p : Fin n → SinglePauli) :
    IsUnitary (pauliMatrix phase p) := by
  rw [pauliMatrix_eq_phase_smul phase p]
  exact unitary_smul_of_phase (Complex.I ^ phase.val) (pauliMatrix (0 : Fin 4) p)
    (i_pow_unit_modulus phase.val) (unphased_pauliMatrix_isUnitary p)

theorem unphased_pauliMatrix_commutation {n : ℕ} (p q : Fin n → SinglePauli) :
    pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) q =
      (∏ i, (p i).commutationSign (q i)) •
        (pauliMatrix (0 : Fin 4) q * pauliMatrix (0 : Fin 4) p) := by
  simp only [pauliMatrix_zero_eq_tensorEntries]
  calc
    tensorEntries (fun i => (p i).matrix) * tensorEntries (fun i => (q i).matrix) =
        tensorEntries (fun i => (p i).matrix * (q i).matrix) :=
      (tensorEntries_mul (fun i => (p i).matrix) (fun i => (q i).matrix)).symm
    _ = tensorEntries (fun i => (p i).commutationSign (q i) •
        ((q i).matrix * (p i).matrix)) := by
      congr 1
      funext i
      exact singlePauli_commutation (p i) (q i)
    _ = (∏ i, (p i).commutationSign (q i)) •
        tensorEntries (fun i => (q i).matrix * (p i).matrix) :=
      tensorEntries_smul (fun i => (p i).commutationSign (q i))
        (fun i => (q i).matrix * (p i).matrix)
    _ = (∏ i, (p i).commutationSign (q i)) •
        (tensorEntries (fun i => (q i).matrix) * tensorEntries (fun i => (p i).matrix)) := by
      rw [tensorEntries_mul]

theorem pauliMatrix_commutation {n : ℕ} (a b : Fin 4) (p q : Fin n → SinglePauli) :
    pauliMatrix a p * pauliMatrix b q =
      (∏ i, (p i).commutationSign (q i)) • (pauliMatrix b q * pauliMatrix a p) := by
  calc
    pauliMatrix a p * pauliMatrix b q =
        ((Complex.I ^ a.val) * (Complex.I ^ b.val)) •
          (pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) q) := by
      rw [pauliMatrix_eq_phase_smul a p, pauliMatrix_eq_phase_smul b q]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm (Complex.I ^ b.val) (Complex.I ^ a.val)]
    _ = (((Complex.I ^ a.val) * (Complex.I ^ b.val)) *
        (∏ i, (p i).commutationSign (q i))) •
          (pauliMatrix (0 : Fin 4) q * pauliMatrix (0 : Fin 4) p) := by
      rw [unphased_pauliMatrix_commutation p q, smul_smul]
    _ = (∏ i, (p i).commutationSign (q i)) • (pauliMatrix b q * pauliMatrix a p) := by
      rw [pauliMatrix_eq_phase_smul b q, pauliMatrix_eq_phase_smul a p]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      ring

theorem pauliMatrix_commute_or_anticommute {n : ℕ}
    (a b : Fin 4) (p q : Fin n → SinglePauli) :
    pauliMatrix a p * pauliMatrix b q = pauliMatrix b q * pauliMatrix a p ∨
      pauliMatrix a p * pauliMatrix b q = -(pauliMatrix b q * pauliMatrix a p) := by
  have hs := prod_signs_eq_one_or_neg_one
    (fun i => (p i).commutationSign (q i))
    (fun i => singlePauli_commutationSign_eq_one_or_neg_one (p i) (q i))
  rcases hs with hs | hs
  · left
    simpa only [hs, one_smul] using pauliMatrix_commutation a b p q
  · right
    simpa only [hs, neg_one_smul] using pauliMatrix_commutation a b p q

end Manuscript
end CriticalDepth
