import CriticalDepth.MatrixCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix

/-!
Rotation lemmas for a concrete Hermitian involution. These are dependencies of
the manuscript's upper construction, not a formalization of its circuit or
stabilizer-code hypotheses.
-/

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rotation (P : Operator ι) (t : ℝ) : Operator ι :=
  affine P (Real.cos t : ℂ) (Complex.I * (Real.sin t : ℂ))

theorem imag_mul_imag (a b : ℂ) :
    (Complex.I * a) * (Complex.I * b) = -(a * b) := by
  calc
    (Complex.I * a) * (Complex.I * b) = (Complex.I * Complex.I) * (a * b) := by ring
    _ = -(a * b) := by rw [Complex.I_mul_I]; ring

@[simp] theorem rotation_zero (P : Operator ι) : rotation P 0 = 1 := by
  simp [rotation, affine]

theorem rotation_add {P : Operator ι} (hP : P * P = 1) (s t : ℝ) :
    rotation P (s + t) = rotation P s * rotation P t := by
  rw [rotation, rotation, rotation, affine_mul hP]
  have hc : (Real.cos (s + t) : ℂ) =
      (Real.cos s : ℂ) * (Real.cos t : ℂ) +
        (Complex.I * (Real.sin s : ℂ)) * (Complex.I * (Real.sin t : ℂ)) := by
    rw [imag_mul_imag, Real.cos_add]
    push_cast
    ring
  have hs : Complex.I * (Real.sin (s + t) : ℂ) =
      (Real.cos s : ℂ) * (Complex.I * (Real.sin t : ℂ)) +
        (Complex.I * (Real.sin s : ℂ)) * (Real.cos t : ℂ) := by
    rw [Real.sin_add]
    push_cast
    ring
  rw [hc, hs]

theorem star_rotation {P : Operator ι} (hP : star P = P) (t : ℝ) :
    star (rotation P t) = rotation P (-t) := by
  have hc : star (Real.cos t : ℂ) = (Real.cos t : ℂ) :=
    Complex.conj_ofReal (Real.cos t)
  have hs : star (Real.sin t : ℂ) = (Real.sin t : ℂ) :=
    Complex.conj_ofReal (Real.sin t)
  have hI : star Complex.I = -Complex.I := by simp
  have hb : star (Complex.I * (Real.sin t : ℂ)) =
      Complex.I * (Real.sin (-t) : ℂ) := by
    rw [star_mul, hs, hI, Real.sin_neg]
    simp only [Complex.ofReal_neg]
    ring
  rw [rotation, star_affine hP, rotation, hc, hb, Real.cos_neg]

theorem rotation_isUnitary {P : Operator ι} (hself : star P = P)
    (hsq : P * P = 1) (t : ℝ) : IsUnitary (rotation P t) := by
  constructor
  · rw [star_rotation hself, ← rotation_add hsq, neg_add_cancel, rotation_zero]
  · rw [star_rotation hself, ← rotation_add hsq, add_neg_cancel, rotation_zero]

theorem continuous_rotation (P : Operator ι) : Continuous (rotation P) := by
  unfold rotation affine
  fun_prop

@[simp] theorem rotation_pi_div_two (P : Operator ι) :
    rotation P (Real.pi / 2) = Complex.I • P := by
  simp [rotation, affine]

theorem rotation_pi_div_two_not_isScalar {P : Operator ι} (hP : ¬ IsScalar P) :
    ¬ IsScalar (rotation P (Real.pi / 2)) := by
  rw [rotation_pi_div_two]
  intro h
  exact hP (isScalar_of_smul Complex.I_ne_zero h)

theorem rotation_pi_div_two_not_projectivelyEquivalent_one
    {P : Operator ι} (hP : ¬ IsScalar P) :
    ¬ ProjectivelyEquivalent (rotation P (Real.pi / 2)) 1 := by
  intro h
  exact rotation_pi_div_two_not_isScalar hP (projectivelyEquivalent_one_isScalar h)

/-- A concrete nontrivial continuous one-parameter unitary family. -/
theorem rotation_one_parameter_family {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hP : ¬ IsScalar P) :
    Continuous (rotation P) ∧
      rotation P 0 = 1 ∧
      (∀ s t : ℝ, rotation P (s + t) = rotation P s * rotation P t) ∧
      (∀ t : ℝ, IsUnitary (rotation P t)) ∧
      ¬ ProjectivelyEquivalent (rotation P (Real.pi / 2)) 1 := by
  exact ⟨continuous_rotation P, rotation_zero P, rotation_add hsq,
    rotation_isUnitary hself hsq, rotation_pi_div_two_not_projectivelyEquivalent_one hP⟩

theorem affine_isUnitary {P : Operator ι} (hself : star P = P)
    (hsq : P * P = 1) {a b : ℂ}
    (hnorm : star a * a + star b * b = 1)
    (hcross : star a * b + star b * a = 0) : IsUnitary (affine P a b) := by
  constructor
  · rw [star_affine hself, affine_mul hsq, hnorm, hcross]
    simp [affine]
  · rw [star_affine hself, affine_mul hsq]
    have hn : a * star a + b * star b = 1 := by simpa [mul_comm] using hnorm
    have hc : a * star b + b * star a = 0 := by simpa [mul_comm, add_comm] using hcross
    rw [hn, hc]
    simp [affine]

noncomputable def rationalScale (r : ℕ) : ℂ :=
  ((Real.sqrt (1 + (r : ℝ) ^ 2) : ℝ) : ℂ)⁻¹

theorem rationalScale_ne_zero (r : ℕ) : rationalScale r ≠ 0 := by
  apply inv_ne_zero
  have hpos : 0 < Real.sqrt (1 + (r : ℝ) ^ 2) := by positivity
  exact_mod_cast ne_of_gt hpos

theorem star_rationalScale (r : ℕ) : star (rationalScale r) = rationalScale r := by
  simp [rationalScale]

theorem rationalScale_sq_mul (r : ℕ) :
    rationalScale r ^ 2 * (1 + (r : ℂ) ^ 2) = 1 := by
  let s : ℂ := (Real.sqrt (1 + (r : ℝ) ^ 2) : ℝ)
  have hsne : s ≠ 0 := by
    dsimp [s]
    have hpos : 0 < Real.sqrt (1 + (r : ℝ) ^ 2) := by positivity
    exact_mod_cast ne_of_gt hpos
  have hs : s ^ 2 = 1 + (r : ℂ) ^ 2 := by
    dsimp [s]
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (r : ℝ) ^ 2 by positivity)
    exact_mod_cast hh
  change (s⁻¹) ^ 2 * (1 + (r : ℂ) ^ 2) = 1
  rw [← hs, ← mul_pow]
  simp [hsne]

/-- A countable family of genuine unitaries, with no matrix-exponential premise. -/
noncomputable def rationalRotation (P : Operator ι) (r : ℕ) : Operator ι :=
  affine P (rationalScale r) (rationalScale r * Complex.I * (r : ℂ))

theorem rationalRotation_isUnitary {P : Operator ι} (hself : star P = P)
    (hsq : P * P = 1) (r : ℕ) : IsUnitary (rationalRotation P r) := by
  let a : ℂ := rationalScale r
  let b : ℂ := a * Complex.I * (r : ℂ)
  have hsa : star a = a := star_rationalScale r
  have hsb : star b = -b := by
    simp [b, a, rationalScale, mul_comm, mul_left_comm, mul_assoc]
  have hbb : b * b = -(a * a * (r : ℂ) ^ 2) := by
    calc
      b * b = (Complex.I * Complex.I) * (a * a * (r : ℂ) ^ 2) := by dsimp [b]; ring
      _ = -(a * a * (r : ℂ) ^ 2) := by rw [Complex.I_mul_I]; ring
  apply affine_isUnitary hself hsq
  · change star a * a + star b * b = 1
    rw [hsa, hsb]
    calc
      a * a + -b * b = a ^ 2 * (1 + (r : ℂ) ^ 2) := by rw [neg_mul, hbb]; ring
      _ = 1 := rationalScale_sq_mul r
  · change star a * b + star b * a = 0
    rw [hsa, hsb]
    ring

theorem rationalRotation_projectivelyEquivalent_injective
    {P : Operator ι} (hP : ¬ IsScalar P) {r s : ℕ}
    (h : ProjectivelyEquivalent (rationalRotation P r) (rationalRotation P s)) : r = s := by
  obtain ⟨z, _, h⟩ := h
  have he : affine P (rationalScale r) (rationalScale r * Complex.I * (r : ℂ)) =
      affine P (z * rationalScale s) (z * (rationalScale s * Complex.I * (s : ℂ))) := by
    simpa [rationalRotation, affine, smul_add, smul_smul] using h
  obtain ⟨h0, h1⟩ := affine_coefficients_unique hP he
  have hprod : (rationalScale r * Complex.I) * (r : ℂ) =
      (rationalScale r * Complex.I) * (s : ℂ) := by
    calc
      (rationalScale r * Complex.I) * (r : ℂ) =
          z * (rationalScale s * Complex.I * (s : ℂ)) := h1
      _ = (z * rationalScale s) * Complex.I * (s : ℂ) := by ring
      _ = (rationalScale r * Complex.I) * (s : ℂ) := by rw [← h0]
  have hc : rationalScale r * Complex.I ≠ 0 :=
    mul_ne_zero (rationalScale_ne_zero r) Complex.I_ne_zero
  have hcast : (r : ℂ) = (s : ℂ) := mul_left_cancel₀ hc hprod
  exact_mod_cast hcast

theorem rationalRotation_classes_injective {P : Operator ι} (hP : ¬ IsScalar P) :
    Function.Injective (fun r : ℕ => projectiveClass (rationalRotation P r)) := by
  intro r s h
  exact rationalRotation_projectivelyEquivalent_injective hP (Quotient.exact h)

theorem rationalRotation_classes_infinite {P : Operator ι} (hP : ¬ IsScalar P) :
    Set.Infinite (Set.range (fun r : ℕ => projectiveClass (rationalRotation P r))) := by
  exact Set.infinite_range_of_injective (rationalRotation_classes_injective hP)

end CriticalDepth
