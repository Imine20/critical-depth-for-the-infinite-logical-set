import CriticalDepth.ScalarConstants
import CriticalDepth.ComponentConstants
import CriticalDepth.IntegralImage
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A derivational criterion for finite algebraic evaluation images

This module combines the scalar-constants criterion, the minimal-prime
integrality argument, and finiteness of evaluations of integral
coordinates. Its derivative-vanishing premise is a substantive hypothesis
to be established from the actual circuit and code equations.
-/

namespace CriticalDepth

universe u v w

variable (F : Type u) (R : Type v)
variable [Field F] [CommRing R] [Algebra F R]

/-- The canonical algebra homomorphism into the fraction ring of an ideal
quotient. A prime ideal will later make the codomain a field. -/
noncomputable def quotientFractionMap (p : Ideal R) :
    R →ₐ[F] FractionRing (R ⧸ p) :=
  (IsScalarTower.toAlgHom F (R ⧸ p) (FractionRing (R ⧸ p))).comp
    (Ideal.Quotient.mkₐ F p)

/-- For a prime ideal, passing from its quotient domain to its fraction
field introduces no further kernel. -/
theorem quotientFractionMap_ker (p : Ideal R) [p.IsPrime] :
    RingHom.ker (quotientFractionMap F R p).toRingHom = p := by
  ext r
  change algebraMap (R ⧸ p) (FractionRing (R ⧸ p))
      (Ideal.Quotient.mk p r) = 0 ↔ r ∈ p
  constructor
  · intro hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p))
    simpa only [map_zero] using hr
  · intro hr
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

section PrimeDerivationCriterion

variable [IsAlgClosed F] [CharZero F] [IsNoetherianRing R]

/-- Vanishing of all base-linear derivatives in the minimal-prime fraction
fields forces an element of a Noetherian algebra to be integral. -/
theorem isIntegral_of_minimalPrime_derivations
    (r : R)
    (h : ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∀ d : Derivation F (FractionRing (R ⧸ p)) (FractionRing (R ⧸ p)),
        d (quotientFractionMap F R p r) = 0) :
    IsIntegral F r := by
  apply isIntegral_of_scalar_mod_minimalPrimes F R r
  intro p hp
  letI : p.IsPrime := hp.isPrime
  let K := FractionRing (R ⧸ p)
  letI : CharZero K := ⟨by
    intro m n hmn
    have hF : (m : F) = (n : F) :=
      (algebraMap F K).injective (by simpa only [map_natCast] using hmn)
    exact Nat.cast_injective hF⟩
  obtain ⟨c, hc⟩ :=
    exists_scalar_mod_kernel_of_forall_derivation_eq_zero F K R
      (quotientFractionMap F R p) r (h p hp)
  refine ⟨c, ?_⟩
  change r - algebraMap F R c ∈
    RingHom.ker (quotientFractionMap F R p).toRingHom at hc
  rw [quotientFractionMap_ker F R p] at hc
  exact hc

/-- A finite collection of coordinates has a finite evaluation image if
all their relative derivatives vanish in every minimal-prime fraction
field. This statement includes nonreduced coordinate algebras. -/
theorem evaluation_image_finite_of_minimalPrime_derivations
    {ι : Type w} [Fintype ι] (r : ι → R)
    (h : ∀ i, ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∀ d : Derivation F (FractionRing (R ⧸ p)) (FractionRing (R ⧸ p)),
        d (quotientFractionMap F R p (r i)) = 0) :
    (Set.range fun f : R →ₐ[F] F => fun i => f (r i)).Finite := by
  apply integral_coordinate_evaluation_image_finite r
  intro i
  exact isIntegral_of_minimalPrime_derivations F R (r i) (h i)

/-- A field-valued formulation of the criterion. This lets an application
prove its derivative identity for arbitrary field-valued solutions of the
coordinate equations and then specialize to the prime fraction fields. -/
theorem evaluation_image_finite_of_all_field_derivations
    {ι : Type w} [Fintype ι] (r : ι → R)
    (h : ∀ (K : Type v) [Field K] [Algebra F K]
      (φ : R →ₐ[F] K) (i : ι) (d : Derivation F K K),
        d (φ (r i)) = 0) :
    (Set.range fun f : R →ₐ[F] F => fun i => f (r i)).Finite := by
  apply evaluation_image_finite_of_minimalPrime_derivations F R r
  intro i p hp d
  letI : p.IsPrime := hp.isPrime
  exact h (FractionRing (R ⧸ p)) (quotientFractionMap F R p) i d

end PrimeDerivationCriterion

end CriticalDepth
