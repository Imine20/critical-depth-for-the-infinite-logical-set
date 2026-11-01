import CriticalDepth.PauliTensor
import CriticalDepth.ProjectiveFaithfulness

/-!
# Pauli strings span every finite-qubit operator space

This is an explicit matrix expansion over complex scalars. It uses all
operators, including non-Hermitian operators, and all physical basis entries.
The code-distance argument can therefore apply it to an arbitrary supported
undetectable operator without adding a Pauli-witness hypothesis.
-/

noncomputable section

namespace CriticalDepth

open Matrix
open scoped BigOperators

theorem matrix_eq_sum_matrixUnits
    {α : Type*} [Fintype α] [DecidableEq α] (A : Operator α) :
    A = ∑ i : α, ∑ j : α, A i j • matrixUnit i j := by
  classical
  funext x y
  simp only [Matrix.sum_apply]
  change A x y = ∑ i : α, ∑ j : α, A i j * (if x = i ∧ y = j then 1 else 0)
  simp [ite_and, mul_ite]

theorem tensorEntries_sum
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] {α β : I → Type*}
    (A : ∀ i, J → Matrix (α i) (β i) ℂ) :
    tensorEntries (fun i => ∑ j : J, A i j) =
      ∑ p : I → J, tensorEntries (fun i => A i (p i)) := by
  classical
  ext x y
  simp only [tensorEntries, Matrix.sum_apply]
  exact Fintype.prod_sum (fun i j => A i j (x i) (y i))

namespace Manuscript

def singlePauliCoefficient (A : Operator (Fin 2)) : SinglePauli → ℂ
  | .I => (A 0 0 + A 1 1) / 2
  | .X => (A 0 1 + A 1 0) / 2
  | .Y => Complex.I * (A 0 1 - A 1 0) / 2
  | .Z => (A 0 0 - A 1 1) / 2

theorem singlePauli_expansion (A : Operator (Fin 2)) :
    A = ∑ p : SinglePauli, singlePauliCoefficient A p • p.matrix := by
  classical
  have hu : (Finset.univ : Finset SinglePauli) = {.I, .X, .Y, .Z} := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hu, singlePauliCoefficient, SinglePauli.matrix] <;>
    ring_nf <;> simp only [pow_two, Complex.I_mul_I] <;> ring

def tensorPauli {I : Type*} [Fintype I] (p : I → SinglePauli) :
    Operator (I → Fin 2) :=
  tensorEntries (fun i => (p i).matrix)

def pauliTensorSpan (I : Type*) [Fintype I] : Submodule ℂ (Operator (I → Fin 2)) :=
  Submodule.span ℂ (Set.range (tensorPauli (I := I)))

theorem matrixUnit_eq_tensorEntries
    {I : Type*} [Fintype I] [DecidableEq I] (x y : I → Fin 2) :
    matrixUnit x y = tensorEntries (fun i => matrixUnit (x i) (y i)) := by
  classical
  ext a b
  by_cases h : a = x ∧ b = y
  · obtain ⟨rfl, rfl⟩ := h
    simp [matrixUnit, tensorEntries]
  · have hex : ∃ i, a i ≠ x i ∨ b i ≠ y i := by
      by_contra hn
      apply h
      constructor
      · funext i
        by_contra hi
        exact hn ⟨i, Or.inl hi⟩
      · funext i
        by_contra hi
        exact hn ⟨i, Or.inr hi⟩
    obtain ⟨i, hi⟩ := hex
    have hzero : (∏ j, matrixUnit (x j) (y j) (a j) (b j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rcases hi with hi | hi <;> simp [matrixUnit, hi]
    simpa [tensorEntries, matrixUnit, h] using hzero.symm

theorem matrixUnit_mem_pauliTensorSpan
    {I : Type*} [Fintype I] [DecidableEq I] (x y : I → Fin 2) :
    matrixUnit x y ∈ pauliTensorSpan I := by
  classical
  rw [matrixUnit_eq_tensorEntries]
  have hlocal : (fun i => matrixUnit (x i) (y i)) =
      (fun i => ∑ p : SinglePauli,
        singlePauliCoefficient (matrixUnit (x i) (y i)) p • p.matrix) := by
    funext i
    exact singlePauli_expansion (matrixUnit (x i) (y i))
  rw [hlocal, tensorEntries_sum]
  apply Submodule.sum_mem
  intro p hp
  rw [tensorEntries_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨p, rfl⟩

theorem tensorPauli_span_eq_top
    {I : Type*} [Fintype I] [DecidableEq I] : pauliTensorSpan I = ⊤ := by
  classical
  apply top_unique
  intro A hA
  rw [matrix_eq_sum_matrixUnits A]
  apply Submodule.sum_mem
  intro x hx
  apply Submodule.sum_mem
  intro y hy
  exact Submodule.smul_mem _ _ (matrixUnit_mem_pauliTensorSpan x y)

theorem unphased_pauliMatrix_span_eq_top (n : ℕ) :
    Submodule.span ℂ (Set.range (fun p : Fin n → SinglePauli => pauliMatrix (0 : Fin 4) p)) =
      (⊤ : Submodule ℂ (Operator (QubitBasis n))) := by
  simp_rw [pauliMatrix_zero_eq_tensorEntries]
  change pauliTensorSpan (Fin n) = ⊤
  exact tensorPauli_span_eq_top

theorem local_pauliTensor_span_eq_top {n : ℕ} (S : Finset (Fin n)) :
    Submodule.span ℂ (Set.range (fun p : S → SinglePauli => tensorEntries (fun i => (p i).matrix))) =
      (⊤ : Submodule ℂ (Operator (LocalBasis (fun _ : Fin n => 2) S))) := by
  change pauliTensorSpan S = ⊤
  exact tensorPauli_span_eq_top

theorem pauliMatrix_eq_localEmbed_of_outside_identity
    {n : ℕ} (S : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ S → p i = .I) :
    pauliMatrix (0 : Fin 4) p =
      localEmbed S (tensorPauli (fun i : S => p i.1)) := by
  classical
  ext x y
  let f : Fin n → ℂ := fun i => (p i).matrix (x i) (y i)
  by_cases hxy : ∀ i, i ∉ S → x i = y i
  · have hprod : (∏ i ∈ S, f i) = ∏ i, f i := by
      apply Finset.prod_subset (Finset.subset_univ S)
      intro i hi hiS
      dsimp [f]
      rw [hout i hiS]
      change (1 : Operator (Fin 2)) (x i) (y i) = 1
      rw [hxy i hiS]
      simp [Matrix.one_apply]
    have hlocal : (∏ i : S, f i.1) = ∏ i ∈ S, f i := Finset.prod_coe_sort S f
    change (Complex.I ^ 0) * (∏ i, f i) =
      if ∀ i, i ∉ S → x i = y i then ∏ i : S, f i.1 else 0
    rw [if_pos hxy, pow_zero, one_mul]
    exact hprod.symm.trans hlocal.symm
  · have hex : ∃ i, i ∉ S ∧ x i ≠ y i := by
      by_contra hn
      apply hxy
      intro i hiS
      by_contra hi
      exact hn ⟨i, hiS, hi⟩
    obtain ⟨i, hiS, hi⟩ := hex
    have hzero : (∏ j, f j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      dsimp [f]
      rw [hout i hiS]
      simp [SinglePauli.matrix, Matrix.one_apply, hi]
    change (Complex.I ^ 0) * (∏ j, f j) =
      if ∀ i, i ∉ S → x i = y i then ∏ i : S, f i.1 else 0
    rw [if_neg hxy, pow_zero, one_mul]
    exact hzero

theorem pauliMatrix_supportedOn_of_outside_identity
    {n : ℕ} (S : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ S → p i = .I) :
    SupportedOn (pauliMatrix (0 : Fin 4) p) S := by
  exact ⟨tensorPauli (fun i : S => p i.1),
    pauliMatrix_eq_localEmbed_of_outside_identity S p hout⟩

def extendLocalPauli {n : ℕ} (S : Finset (Fin n)) (p : S → SinglePauli) :
    Fin n → SinglePauli :=
  fun i => if hi : i ∈ S then p ⟨i, hi⟩ else .I

theorem pauliMatrix_extendLocalPauli_eq_localEmbed
    {n : ℕ} (S : Finset (Fin n)) (p : S → SinglePauli) :
    pauliMatrix (0 : Fin 4) (extendLocalPauli S p) = localEmbed S (tensorPauli p) := by
  classical
  have hout : ∀ i, i ∉ S → extendLocalPauli S p i = .I := by
    intro i hi
    simp [extendLocalPauli, hi]
  have hrestrict : (fun i : S => extendLocalPauli S p i.1) = p := by
    funext i
    simp [extendLocalPauli, i.2]
  have h := pauliMatrix_eq_localEmbed_of_outside_identity S (extendLocalPauli S p) hout
  simpa only [hrestrict] using h

theorem pauliMatrix_extendLocalPauli_supportedOn
    {n : ℕ} (S : Finset (Fin n)) (p : S → SinglePauli) :
    SupportedOn (pauliMatrix (0 : Fin 4) (extendLocalPauli S p)) S := by
  exact ⟨tensorPauli p, pauliMatrix_extendLocalPauli_eq_localEmbed S p⟩

end Manuscript
end CriticalDepth
