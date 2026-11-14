import CriticalDepthMathlib
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Irrationality of the two-axis Clifford–T eigenangle
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

/-- The algebraic trace of the product of two π/8 rotations cannot be the
sum of a root of unity and its inverse. -/
theorem not_integral_one_add_sqrt_two_half :
    ¬ IsIntegral ℤ (1 + (Real.sqrt 2 : ℂ) / 2) := by
  intro h
  have hbase : IsIntegral ℤ ((Real.sqrt 2 : ℂ) / 2) := by
    have hi : IsIntegral ℤ ((1 + (Real.sqrt 2 : ℂ) / 2) - 1) := h.sub isIntegral_one
    simpa using hi
  have hs : ((Real.sqrt 2 : ℂ) / 2) ^ 2 = (1 / 2 : ℂ) := by
    have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [div_pow, hsqrt]
    norm_num
  have hhalf : IsIntegral ℤ ((1 / 2 : ℚ) : ℂ) := by
    have hcast : ((1 / 2 : ℚ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hcast, ← hs]
    exact hbase.pow 2
  have hRat : IsIntegral ℤ (1 / 2 : ℚ) := isIntegral_ratCast_iff.mp hhalf
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hRat
  have hz' : (z : ℚ) = 1 / 2 := hz
  have hz2 : (z : ℚ) * 2 = 1 := (eq_div_iff (by norm_num)).mp hz'
  have hzi : z * 2 = 1 := by exact_mod_cast hz2
  omega

/-- An angle with the trace of the product of the two quarter-turn
generators is not a rational multiple of π. -/
theorem irrational_angle_of_trace (θ : ℝ)
    (hTrace : (2 : ℝ) * Real.cos θ = 1 + Real.sqrt 2 / 2) :
    Irrational (θ / Real.pi) := by
  intro hRat
  obtain ⟨r, hr⟩ := hRat
  have hθ : θ = (r : ℝ) * Real.pi := by
    exact (div_eq_iff (ne_of_gt Real.pi_pos)).mp hr.symm
  let p : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  let m : ℕ := 2 * r.den
  have hm : 0 < m := by dsimp [m]; positivity
  have hArg : (m : ℝ) * θ = (r.num : ℝ) * (2 * Real.pi) := by
    rw [hθ, Rat.cast_def]
    unfold m
    push_cast
    have hden : (r.den : ℝ) ≠ 0 := by positivity
    field_simp <;> ring
  have hOrder : p ^ m = 1 := by
    unfold p
    rw [← Complex.exp_nat_mul, show (m : ℂ) * ((θ : ℂ) * Complex.I) =
        (((m : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring, hArg]
    push_cast
    calc
      Complex.exp ((r.num : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I) =
          Complex.exp ((r.num : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
        congr 1
        ring
      _ = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I)) ^ r.num :=
        Complex.exp_int_mul _ _
      _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]
  have hp : IsIntegral ℤ p := IsIntegral.of_pow hm (hOrder ▸ isIntegral_one)
  have hk : IsIntegral ℤ (star p) := by
    have hs : (star p) ^ m = 1 := by
      rw [← star_pow, hOrder, star_one]
    exact IsIntegral.of_pow hm (hs ▸ isIntegral_one)
  have he : p + star p = 1 + (Real.sqrt 2 : ℂ) / 2 := by
    unfold p
    rw [Complex.exp_ofReal_mul_I]
    have hℂ : ((2 : ℂ) * (Real.cos θ : ℂ)) = 1 + (Real.sqrt 2 : ℂ) / 2 := by
      exact_mod_cast hTrace
    rw [← hℂ]
    change (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I +
      starRingEnd ℂ ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) = _
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  apply not_integral_one_add_sqrt_two_half
  rw [← he]
  exact hp.add hk

#print axioms not_integral_one_add_sqrt_two_half
#print axioms irrational_angle_of_trace

end CriticalDepth.Manuscript20261114.CliffordT
