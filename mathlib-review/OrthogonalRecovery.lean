import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# Terminal recovery for orthogonal isometric error branches

This is the diagonal Knill–Laflamme case. The reset construction follows
the projection-complement argument in `KrausCompletion.lean` of the Yimin
Formalization Toolbox, adapted here to rectangular matrices. The resulting
finite Kraus family is proved trace preserving through its completeness
identity and acts as the identity on every listed error branch. The source
does not yet connect this family to the manuscript's optimization over
all CPTP maps or prove the reduction from a general Gram matrix.
-/

namespace CriticalDepth.OrthogonalRecovery

noncomputable section

open scoped BigOperators
open Matrix

variable {Phys Log Hist : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Fintype Hist]

private def sector (A : Hist → Matrix Phys Log ℂ) (s : Hist) : Matrix Phys Phys ℂ :=
  A s * (A s).conjTranspose

private def remainder (A : Hist → Matrix Phys Log ℂ) : Matrix Phys Phys ℂ :=
  1 - ∑ s, sector A s

private def resetRow (state : Log → ℂ) (j : Phys) : Matrix Log Phys ℂ :=
  fun a b => if b = j then state a else 0

private def resetKraus (A : Hist → Matrix Phys Log ℂ) (state : Log → ℂ)
    (j : Phys) : Matrix Log Phys ℂ :=
  resetRow state j * remainder A

private def recoveryKraus (A : Hist → Matrix Phys Log ℂ) (state : Log → ℂ) :
    Hist ⊕ Phys → Matrix Log Phys ℂ
  | .inl s => (A s).conjTranspose
  | .inr j => resetKraus A state j

private theorem sector_mul_branch [DecidableEq Hist] (A : Hist → Matrix Phys Log ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0) (s t : Hist) :
    sector A s * A t = if s = t then A t else 0 := by
  classical
  by_cases h : s = t
  · subst s
    simp [sector, Matrix.mul_assoc, hiso]
  · simp [sector, Matrix.mul_assoc, h, horth _ _ h]

private theorem sector_sum_mul_branch (A : Hist → Matrix Phys Log ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0) (t : Hist) :
    (∑ s, sector A s) * A t = A t := by
  classical
  rw [Matrix.sum_mul]
  simp only [sector_mul_branch A hiso horth]
  simp

omit [Fintype Phys] [DecidableEq Log] in
private theorem remainder_selfAdjoint (A : Hist → Matrix Phys Log ℂ) :
    (remainder A).conjTranspose = remainder A := by
  simp only [remainder, sector, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

private theorem remainder_mul_branch (A : Hist → Matrix Phys Log ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0) (t : Hist) :
    remainder A * A t = 0 := by
  rw [remainder, Matrix.sub_mul, Matrix.one_mul, sector_sum_mul_branch A hiso horth t, sub_self]

private theorem remainder_idempotent (A : Hist → Matrix Phys Log ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0) :
    remainder A * remainder A = remainder A := by
  have hzero : remainder A * (∑ s, sector A s) = 0 := by
    rw [Matrix.mul_sum]
    apply Finset.sum_eq_zero
    intro s _
    simp only [sector, ← Matrix.mul_assoc, remainder_mul_branch A hiso horth s,
      Matrix.zero_mul]
  change remainder A * (1 - ∑ s, sector A s) = remainder A
  rw [Matrix.mul_sub, Matrix.mul_one, hzero, sub_zero]

omit [DecidableEq Log] in
private theorem resetRow_complete (state : Log → ℂ)
    (hstate : ∑ a, star (state a) * state a = 1) :
    (∑ j, (resetRow (Phys := Phys) state j).conjTranspose * resetRow state j) = 1 := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, resetRow] using hstate
  · rw [Matrix.sum_apply]
    have hz (j : Phys) : ((resetRow state j).conjTranspose * resetRow state j) a b = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      simp only [Matrix.conjTranspose_apply, resetRow]
      split_ifs <;> simp_all
    simp [hz, hab]

private theorem resetKraus_complete (A : Hist → Matrix Phys Log ℂ) (state : Log → ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0)
    (hstate : ∑ a, star (state a) * state a = 1) :
    (∑ j, (resetKraus A state j).conjTranspose * resetKraus A state j) = remainder A := by
  calc
    _ = (remainder A).conjTranspose *
        (∑ j, (resetRow state j).conjTranspose * resetRow state j) * remainder A := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [resetKraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = remainder A := by
      rw [resetRow_complete state hstate, Matrix.mul_one, remainder_selfAdjoint,
        remainder_idempotent A hiso horth]

/-- Complete the orthogonal isometries to a single recovery with
specified scalar action on every branch. -/
theorem existsRecoveryKraus_scalar (A : Hist → Matrix Phys Log ℂ) (state : Log → ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0)
    (hstate : ∑ a, star (state a) * state a = 1) :
    ∃ R : Hist ⊕ Phys → Matrix Log Phys ℂ,
      (∑ k, (R k).conjTranspose * R k) = 1 ∧
      ∃ z : (Hist ⊕ Phys) → Hist → ℂ, ∀ k t, R k * A t = z k t • (1 : Matrix Log Log ℂ) := by
  classical
  refine ⟨recoveryKraus A state, ?_, fun k t => if k = Sum.inl t then 1 else 0, ?_⟩
  · rw [Fintype.sum_sum_type]
    simp only [recoveryKraus, Matrix.conjTranspose_conjTranspose,
      resetKraus_complete A state hiso horth hstate, remainder, sector]
    abel
  · intro k t
    cases k with
    | inl s =>
      by_cases h : s = t
      · subst s
        simp [recoveryKraus, hiso]
      · simp [recoveryKraus, h, horth s t h]
    | inr j =>
      simp [recoveryKraus, resetKraus, Matrix.mul_assoc, remainder_mul_branch A hiso horth]

/-- Complete a family of orthogonal error isometries to one recovery. The
witness simultaneously inverts every error branch and sends each remaining
physical basis coordinate to the same normalized logical reset state. -/
theorem existsRecoveryKraus (A : Hist → Matrix Phys Log ℂ) (state : Log → ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0)
    (hstate : ∑ a, star (state a) * state a = 1) :
    ∃ R : Hist ⊕ Phys → Matrix Log Phys ℂ,
      (∑ k, (R k).conjTranspose * R k) = 1 ∧
      ∀ (t : Hist) (X : Matrix Log Log ℂ),
        (∑ k, R k * (A t * X * (A t).conjTranspose) * (R k).conjTranspose) = X := by
  classical
  refine ⟨recoveryKraus A state, ?_, ?_⟩
  · rw [Fintype.sum_sum_type]
    simp only [recoveryKraus, Matrix.conjTranspose_conjTranspose,
      resetKraus_complete A state hiso horth hstate]
    simp only [remainder, sector]
    abel
  · intro t X
    have hcompose (k : Hist ⊕ Phys) :
        recoveryKraus A state k * A t = if k = Sum.inl t then 1 else 0 := by
      cases k with
      | inl s =>
        by_cases h : s = t
        · subst s
          simp [recoveryKraus, hiso]
        · simp [recoveryKraus, h, horth s t h]
      | inr j =>
        simp [recoveryKraus, resetKraus, Matrix.mul_assoc, remainder_mul_branch A hiso horth]
    have hrewrite (k : Hist ⊕ Phys) :
        recoveryKraus A state k * (A t * X * (A t).conjTranspose) *
          (recoveryKraus A state k).conjTranspose =
        (recoveryKraus A state k * A t) * X *
          (recoveryKraus A state k * A t).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [hrewrite, hcompose]
    rw [Finset.sum_eq_single (Sum.inl t)]
    · simp
    · intro k _ hne
      simp [hne]
    · simp

example (A : Unit → Matrix (Fin 3) (Fin 2) ℂ)
    (hiso : ∀ s, (A s).conjTranspose * A s = 1) :
    ∃ R : Unit ⊕ Fin 3 → Matrix (Fin 2) (Fin 3) ℂ,
      (∑ k, (R k).conjTranspose * R k) = 1 ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        (∑ k, R k * (A () * X * (A ()).conjTranspose) * (R k).conjTranspose) = X := by
  obtain ⟨R, hcomplete, hrestore⟩ := existsRecoveryKraus A ![1, 0] hiso
    (fun s t h => False.elim (h (Subsingleton.elim _ _))) (by simp [Fin.sum_univ_two])
  exact ⟨R, hcomplete, hrestore ()⟩

#print axioms existsRecoveryKraus_scalar
#print axioms existsRecoveryKraus

end

end CriticalDepth.OrthogonalRecovery
