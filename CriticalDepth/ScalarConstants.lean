import CriticalDepth.FieldConstants
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Scalar values of derivation constants

An algebraic element of a field extension of an algebraically closed field
comes from the base field. Combined with the differential-constants
criterion, this identifies the scalar value of a coordinate annihilated
by every base-linear derivation.
-/

namespace CriticalDepth

open Polynomial

universe u v w

variable (F : Type u) (K : Type v)
variable [Field F] [IsAlgClosed F] [Field K] [Algebra F K]

/-- An individual algebraic element over an algebraically closed field
is the image of a scalar from that field. No algebraicity assumption on
the whole ambient extension is imposed. -/
theorem exists_algebraMap_eq_of_isAlgebraic
    (a : K) (ha : IsAlgebraic F a) :
    ∃ c : F, algebraMap F K c = a := by
  have hi : IsIntegral F a := ha.isIntegral
  refine ⟨-(minpoly F a).coeff 0, ?_⟩
  have hq : (minpoly F a).leadingCoeff = 1 := minpoly.monic hi
  have hdeg : (minpoly F a).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hi)
  have hroot : aeval a (minpoly F a) = 0 := minpoly.aeval F a
  rw [eq_X_add_C_of_degree_eq_one hdeg, hq, C_1, one_mul,
    aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at hroot
  simpa only [map_neg] using hroot.symm

/-- In a characteristic-zero extension of an algebraically closed field,
an element annihilated by every base-linear derivation is a base scalar. -/
theorem exists_algebraMap_eq_of_forall_derivation_eq_zero
    [CharZero K] (a : K)
    (h : ∀ d : Derivation F K K, d a = 0) :
    ∃ c : F, algebraMap F K c = a :=
  exists_algebraMap_eq_of_isAlgebraic F K a
    (isAlgebraic_of_forall_derivation_eq_zero F K a h)

/-- A scalar value after an algebra homomorphism gives a scalar congruence
modulo its kernel. This applies in particular to the map from a coordinate
algebra to the fraction field of a prime quotient. -/
theorem exists_scalar_mod_kernel_of_forall_derivation_eq_zero
    [CharZero K] (R : Type w) [CommRing R] [Algebra F R]
    (φ : R →ₐ[F] K) (r : R)
    (h : ∀ d : Derivation F K K, d (φ r) = 0) :
    ∃ c : F, r - algebraMap F R c ∈ RingHom.ker φ.toRingHom := by
  obtain ⟨c, hc⟩ :=
    exists_algebraMap_eq_of_forall_derivation_eq_zero F K (φ r) h
  refine ⟨c, ?_⟩
  change φ (r - algebraMap F R c) = 0
  rw [map_sub, φ.commutes, hc, sub_self]

end CriticalDepth
