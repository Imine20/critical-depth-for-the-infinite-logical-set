import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
Concrete matrix conventions shared by the critical-depth development.

`ProjectivelyEquivalent` removes exactly one global unit-modulus complex
scalar. `IsScalar` does not allow different phases on separate sectors.
-/

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Operator (ι : Type*) := Matrix ι ι ℂ

def IsScalar (A : Operator ι) : Prop :=
  ∃ z : ℂ, A = z • (1 : Operator ι)

def ProjectivelyEquivalent (A B : Operator ι) : Prop :=
  ∃ z : ℂ, star z * z = 1 ∧ A = z • B

/-- Both inverse equations are recorded, with the adjoint on the left first. -/
def IsUnitary (A : Operator ι) : Prop :=
  star A * A = 1 ∧ A * star A = 1

def affine (P : Operator ι) (a b : ℂ) : Operator ι :=
  a • (1 : Operator ι) + b • P

theorem projectivelyEquivalent_refl (A : Operator ι) :
    ProjectivelyEquivalent A A := by
  exact ⟨1, by simp, by simp⟩

theorem projectivelyEquivalent_symm {A B : Operator ι}
    (h : ProjectivelyEquivalent A B) : ProjectivelyEquivalent B A := by
  obtain ⟨z, hz, hAB⟩ := h
  refine ⟨star z, ?_, ?_⟩
  · simpa [mul_comm] using hz
  · calc
      B = (star z * z) • B := by rw [hz]; simp
      _ = star z • (z • B) := by rw [smul_smul]
      _ = star z • A := by rw [hAB]

theorem projectivelyEquivalent_trans {A B C : Operator ι}
    (hAB : ProjectivelyEquivalent A B) (hBC : ProjectivelyEquivalent B C) :
    ProjectivelyEquivalent A C := by
  obtain ⟨z, hz, hAB⟩ := hAB
  obtain ⟨w, hw, hBC⟩ := hBC
  refine ⟨z * w, ?_, ?_⟩
  · calc
      star (z * w) * (z * w) = (star z * z) * (star w * w) := by
        rw [star_mul]
        ring
      _ = 1 := by rw [hz, hw]; simp
  · rw [hAB, hBC, smul_smul]

def projectiveSetoid (ι : Type*) [Fintype ι] [DecidableEq ι] : Setoid (Operator ι) where
  r := ProjectivelyEquivalent
  iseqv := ⟨projectivelyEquivalent_refl, projectivelyEquivalent_symm,
    projectivelyEquivalent_trans⟩

abbrev ProjectiveOperator (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  Quotient (projectiveSetoid ι)

def projectiveClass (A : Operator ι) : ProjectiveOperator ι :=
  Quotient.mk (projectiveSetoid ι) A

theorem projectivelyEquivalent_one_isScalar {A : Operator ι}
    (h : ProjectivelyEquivalent A 1) : IsScalar A := by
  obtain ⟨z, _, hz⟩ := h
  exact ⟨z, hz⟩

theorem isScalar_of_smul {P : Operator ι} {z : ℂ} (hz : z ≠ 0)
    (h : IsScalar (z • P)) : IsScalar P := by
  obtain ⟨a, ha⟩ := h
  refine ⟨z⁻¹ * a, ?_⟩
  calc
    P = z⁻¹ • (z • P) := by simp [smul_smul, hz]
    _ = z⁻¹ • (a • (1 : Operator ι)) := by rw [ha]
    _ = (z⁻¹ * a) • (1 : Operator ι) := by rw [smul_smul]

/-- A nonscalar matrix and the identity are linearly independent. -/
theorem affine_eq_zero_coefficients {P : Operator ι} (hP : ¬ IsScalar P)
    {a b : ℂ} (h : affine P a b = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply hP
    have hbp : b • P = -(a • (1 : Operator ι)) := by
      have hh := congrArg (fun X : Operator ι => X - a • (1 : Operator ι)) h
      simpa [affine, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh
    refine ⟨-(b⁻¹ * a), ?_⟩
    calc
      P = b⁻¹ • (b • P) := by simp [smul_smul, hb]
      _ = b⁻¹ • (-(a • (1 : Operator ι))) := by rw [hbp]
      _ = (-(b⁻¹ * a)) • (1 : Operator ι) := by simp [smul_smul]
  subst b
  constructor
  · by_contra ha
    have hone : (1 : Operator ι) = 0 := by
      have hh := congrArg (fun X : Operator ι => a⁻¹ • X) h
      simpa [affine, smul_smul, ha] using hh
    apply hP
    refine ⟨0, ?_⟩
    have hzero : P = 0 := by
      calc
        P = P * 1 := by simp
        _ = P * 0 := by rw [hone]
        _ = 0 := by simp
    simpa using hzero
  · rfl

theorem affine_coefficients_unique {P : Operator ι} (hP : ¬ IsScalar P)
    {a b c d : ℂ} (h : affine P a b = affine P c d) : a = c ∧ b = d := by
  have hzero : affine P (a - c) (b - d) = 0 := by
    calc
      affine P (a - c) (b - d) = affine P a b - affine P c d := by
        simp only [affine, sub_smul]
        abel
      _ = 0 := sub_eq_zero.mpr h
  obtain ⟨ha, hb⟩ := affine_eq_zero_coefficients hP hzero
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩

theorem affine_mul {P : Operator ι} (hP : P * P = 1)
    (a b c d : ℂ) :
    affine P a b * affine P c d = affine P (a * c + b * d) (a * d + b * c) := by
  simp only [affine, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, mul_one, one_mul, hP, add_smul]
  simp only [mul_comm c a, mul_comm c b, mul_comm d a, mul_comm d b]
  abel

theorem star_affine {P : Operator ι} (hP : star P = P) (a b : ℂ) :
    star (affine P a b) = affine P (star a) (star b) := by
  simp [affine, hP]

end CriticalDepth
