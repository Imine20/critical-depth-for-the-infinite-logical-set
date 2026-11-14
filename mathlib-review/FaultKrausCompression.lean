import FaultKrausCompactness

/-!
# Exact compression of a finite Kraus family

Factor the positive semidefinite Choi Gram matrix on the fixed
`logical × physical` coordinate set. The square factor induces a new
Kraus family on that index, with exactly the same channel and encoded
branch losses even when the original set of operators was larger.
-/

namespace CriticalDepth.FaultKrausCompression

noncomputable section

open Matrix
open FaultEntanglementFidelity
open FaultKrausCompactness
open scoped BigOperators ComplexOrder

variable {Phys Log Rec : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Fintype Rec]

private def columns (R : Rec → Matrix Log Phys ℂ) : Matrix (Log × Phys) Rec ℂ :=
  Matrix.of (fun p k => R k p.1 p.2)

private def gram (R : Rec → Matrix Log Phys ℂ) : Matrix (Log × Phys) (Log × Phys) ℂ :=
  columns R * (columns R).conjTranspose

private theorem gram_apply (R : Rec → Matrix Log Phys ℂ) (p q : Log × Phys) :
    gram R p q = ∑ k, R k p.1 p.2 * star (R k q.1 q.2) := by
  simp [gram, columns, Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem squareFactor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, B * B.conjTranspose = A := by
  let V := hA.1.eigenvectorUnitary
  let sqrtD := Matrix.diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ))
  refine ⟨(V : Matrix ι ι ℂ) * sqrtD, ?_⟩
  have hs : sqrtD.conjTranspose = sqrtD := by
    simp [sqrtD, Matrix.diagonal_conjTranspose, Pi.star_apply, Complex.conj_ofReal]
  have hd : sqrtD * sqrtD = Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ)) := by
    rw [show sqrtD = Matrix.diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) by rfl,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  have hSpectral : (V : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ)) *
      (V : Matrix ι ι ℂ).conjTranspose = A := by
    symm
    simpa only [V, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hA.1.spectral_theorem
  calc
    _ = (V : Matrix ι ι ℂ) * (sqrtD * sqrtD) * (V : Matrix ι ι ℂ).conjTranspose := by
      rw [Matrix.conjTranspose_mul, hs]
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hd, hSpectral]

private theorem channel_entry (R : Rec → Matrix Log Phys ℂ) (A : Matrix Phys Phys ℂ)
    (a b : Log) :
    (∑ k, R k * A * (R k).conjTranspose) a b =
      ∑ j : Phys, ∑ i : Phys, A i j * gram R (a, i) (b, j) := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, gram_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem gram_eq_imp_channel_eq {Rec' : Type*} [Fintype Rec']
    (R : Rec → Matrix Log Phys ℂ) (S : Rec' → Matrix Log Phys ℂ)
    (h : gram R = gram S) (A : Matrix Phys Phys ℂ) :
    (∑ k, R k * A * (R k).conjTranspose) =
      ∑ k, S k * A * (S k).conjTranspose := by
  apply Matrix.ext
  intro a b
  calc
    _ = ∑ j : Phys, ∑ i : Phys, A i j * gram R (a, i) (b, j) := channel_entry R A a b
    _ = ∑ j : Phys, ∑ i : Phys, A i j * gram S (a, i) (b, j) := by rw [h]
    _ = _ := (channel_entry S A a b).symm

private theorem completeness_entry (R : Rec → Matrix Log Phys ℂ) (i j : Phys) :
    ((∑ k, (R k).conjTranspose * R k) : Matrix Phys Phys ℂ) i j =
      ∑ a : Log, gram R (a, j) (a, i) := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, gram_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

private theorem gram_eq_imp_completeness_eq {Rec' : Type*} [Fintype Rec']
    (R : Rec → Matrix Log Phys ℂ) (S : Rec' → Matrix Log Phys ℂ) (h : gram R = gram S) :
    (∑ k, (R k).conjTranspose * R k) =
      ∑ k, (S k).conjTranspose * S k := by
  apply Matrix.ext
  intro i j
  calc
    _ = ∑ a : Log, gram R (a, j) (a, i) := completeness_entry R i j
    _ = ∑ a : Log, gram S (a, j) (a, i) := by rw [h]
    _ = _ := (completeness_entry S i j).symm

private theorem loss_numerator (R : Rec → Matrix Log Phys ℂ) (A : Matrix Phys Log ℂ) :
    (∑ k, Complex.normSq (R k * A).trace) =
      (∑ j : Log × Phys, ∑ i : Log × Phys, A i.2 i.1 *
        star (A j.2 j.1) * gram R i j).re := by
  have hTrace (k : Rec) : (R k * A).trace =
      ∑ i : Log × Phys, R k i.1 i.2 * A i.2 i.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  have hC :
      (∑ k, (Complex.normSq (R k * A).trace : ℂ)) =
        ∑ j : Log × Phys, ∑ i : Log × Phys, A i.2 i.1 *
          star (A j.2 j.1) * gram R i j := by
    simp only [Complex.normSq_eq_conj_mul_self, hTrace, map_sum, map_mul, gram_apply,
      Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ i : Log × Phys, ∑ j : Log × Phys, ∑ k : Rec,
          ((starRingEnd ℂ) (R k j.1 j.2) * (starRingEnd ℂ) (A j.2 j.1)) *
            (R k i.1 i.2 * A i.2 i.1) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ j : Log × Phys, ∑ i : Log × Phys, ∑ k : Rec,
          ((starRingEnd ℂ) (R k j.1 j.2) * (starRingEnd ℂ) (A j.2 j.1)) *
            (R k i.1 i.2 * A i.2 i.1) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        change (star (R k j.1 j.2) * star (A j.2 j.1)) *
            (R k i.1 i.2 * A i.2 i.1) =
          A i.2 i.1 * star (A j.2 j.1) * (R k i.1 i.2 * star (R k j.1 j.2))
        ring
  simpa only [Complex.re_sum, Complex.ofReal_re] using congrArg Complex.re hC

private theorem gram_eq_imp_encodedLoss_eq {Rec' : Type*} [Fintype Rec']
    (R : Rec → Matrix Log Phys ℂ) (S : Rec' → Matrix Log Phys ℂ) (h : gram R = gram S)
    (A : Matrix Phys Log ℂ) :
    loss (fun k => R k * A) = loss (fun k => S k * A) := by
  have hNum : (∑ k, Complex.normSq (R k * A).trace) =
      ∑ k, Complex.normSq (S k * A).trace := by
    calc
      _ = (∑ j : Log × Phys, ∑ i : Log × Phys, A i.2 i.1 *
        star (A j.2 j.1) * gram R i j).re := loss_numerator R A
      _ = (∑ j : Log × Phys, ∑ i : Log × Phys, A i.2 i.1 *
        star (A j.2 j.1) * gram S i j).re := by rw [h]
      _ = _ := (loss_numerator S A).symm
  unfold loss fidelity
  simp only [hNum]

/-- Every finite rectangular Kraus family admits an equally acting family
indexed by the output–input coordinate pair. The witness preserves its
full linear map, completeness operator, and all encoded branch losses. -/
theorem exists_compressedKraus (R : Rec → Matrix Log Phys ℂ) :
    ∃ S : (Log × Phys) → Matrix Log Phys ℂ,
      (∀ A : Matrix Phys Phys ℂ,
        (∑ k, R k * A * (R k).conjTranspose) = ∑ k, S k * A * (S k).conjTranspose) ∧
      (∑ k, (R k).conjTranspose * R k) = (∑ k, (S k).conjTranspose * S k) ∧
      ∀ A : Matrix Phys Log ℂ, loss (fun k => R k * A) = loss (fun k => S k * A) := by
  obtain ⟨B, hB⟩ := squareFactor (gram R) (Matrix.posSemidef_self_mul_conjTranspose (columns R))
  let S : (Log × Phys) → Matrix Log Phys ℂ := fun k => Matrix.of (fun i j => B (i, j) k)
  have hColumns : columns S = B := by
    ext ⟨i, j⟩ k
    rfl
  have hGram : gram R = gram S := by
    unfold gram
    rw [hColumns]
    exact hB.symm
  exact ⟨S, gram_eq_imp_channel_eq R S hGram, gram_eq_imp_completeness_eq R S hGram,
    gram_eq_imp_encodedLoss_eq R S hGram⟩

/-- A compact fixed-index optimization gives an optimal recovery over the
union of all finite Kraus index sizes, with no loss of accuracy. -/
theorem exists_minimum_all_finiteKraus {Hist : Type*} [Nonempty Log]
    (histories : Finset Hist) (w : Hist → ℝ) (A : Hist → Matrix Phys Log ℂ) :
    ∃ S : (Log × Phys) → Matrix Log Phys ℂ,
      S ∈ tpFamilies ∧
      ∀ r : ℕ, ∀ T : Fin r → Matrix Log Phys ℂ, T ∈ tpFamilies →
        (∑ i ∈ histories, w i * loss (fun k => S k * A i)) ≤
          (∑ i ∈ histories, w i * loss (fun k => T k * A i)) := by
  classical
  let j₀ : Log := Classical.choice inferInstance
  let S₀ : (Log × Phys) → Matrix Log Phys ℂ :=
    fun k => Matrix.single j₀ k.2 (if k.1 = j₀ then 1 else 0)
  have hS₀ : S₀ ∈ tpFamilies := by
    change (∑ k, (S₀ k).conjTranspose * S₀ k) = 1
    have hprod (k : Log × Phys) : (S₀ k).conjTranspose * S₀ k =
        if k.1 = j₀ then Matrix.single k.2 k.2 1 else 0 := by
      by_cases hk : k.1 = j₀
      · simp [S₀, hk]
      · simp [S₀, hk]
    simp_rw [hprod, Fintype.sum_prod_type]
    have hOuter : (∑ c : Log, ∑ a : Phys,
        if c = j₀ then (Matrix.single a a 1 : Matrix Phys Phys ℂ) else 0) =
        ∑ a : Phys, (Matrix.single a a 1 : Matrix Phys Phys ℂ) := by
      rw [Finset.sum_eq_single j₀]
      · simp
      · intro c _ hc
        simp [hc]
      · simp
    rw [hOuter]
    apply Matrix.ext
    intro a b
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst b
      rw [Finset.sum_eq_single a]
      · simp [Matrix.single]
      · intro c _ hc
        simp [Matrix.single, hc]
      · simp
    · have hz (c : Phys) : (Matrix.single c c 1 : Matrix Phys Phys ℂ) a b = 0 := by
        by_cases hc : c = a
        · subst c
          simp [Matrix.single, hab]
        · simp [Matrix.single, hc]
      simp only [hz, Finset.sum_const_zero, if_neg hab]
  obtain ⟨S, hS, hopt⟩ := exists_minimum_historyLoss histories w A ⟨S₀, hS₀⟩
  refine ⟨S, hS, ?_⟩
  intro r T hT
  obtain ⟨T', _, hTP, hLoss⟩ := exists_compressedKraus T
  have hT' : T' ∈ tpFamilies := hTP.symm.trans hT
  simpa only [hLoss] using hopt T' hT'

#print axioms exists_compressedKraus
#print axioms exists_minimum_all_finiteKraus

end

end CriticalDepth.FaultKrausCompression
