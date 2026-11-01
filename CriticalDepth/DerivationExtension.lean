import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Extending derivations through a formally etale algebra

The extension below is obtained from the universal property of Kahler
differentials and the base-change equivalence for a formally etale map.
It is an algebraic ingredient of the proposed proof of finiteness of the
logical image; this module does not assert either manuscript theorem.
-/

namespace CriticalDepth

universe u v w

variable (R : Type u) (S : Type v) (T : Type w)
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T]
variable [IsScalarTower R S T] [Algebra.FormallyEtale S T]

/-- Extend an `R`-derivation from `S` to `T` through a formally etale map.
The codomain is already `T`, so the tensor base change can be evaluated
directly in that codomain. -/
noncomputable def extendDerivationFormallyEtale
    (d : Derivation R S T) : Derivation R T T :=
  ((d.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

/-- The extended derivation agrees with the given derivation on scalars
coming from `S`. -/
theorem extendDerivationFormallyEtale_algebraMap
    (d : Derivation R S T) (s : S) :
    extendDerivationFormallyEtale R S T d (algebraMap S T s) = d s := by
  change (d.liftKaehlerDifferential.liftBaseChange T)
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
        (KaehlerDifferential.D R T (algebraMap S T s))) = d s
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

section PolynomialCoordinates

variable (σ : Type v)
variable [Algebra (MvPolynomial σ R) T]
variable [IsScalarTower R (MvPolynomial σ R) T]
variable [Algebra.FormallyEtale (MvPolynomial σ R) T]

/-- The partial derivation in one polynomial coordinate, extended through
a formally etale algebra. No finiteness assumption on the variable type
is needed. -/
noncomputable def polynomialCoordinateDerivation
    (i : σ) : Derivation R T T :=
  extendDerivationFormallyEtale R (MvPolynomial σ R) T
    ((Algebra.linearMap (MvPolynomial σ R) T).compDer (MvPolynomial.pderiv i))

/-- The extended partial derivation sends its chosen coordinate to one. -/
theorem polynomialCoordinateDerivation_X (i : σ) :
    polynomialCoordinateDerivation R T σ i
      (algebraMap (MvPolynomial σ R) T (MvPolynomial.X i)) = 1 := by
  rw [polynomialCoordinateDerivation,
    extendDerivationFormallyEtale_algebraMap]
  change algebraMap (MvPolynomial σ R) T
      (MvPolynomial.pderiv i (MvPolynomial.X i)) = 1
  rw [MvPolynomial.pderiv_X_self, map_one]

/-- A polynomial coordinate cannot be annihilated by every base-linear
derivation after a formally etale extension to a nontrivial ring. -/
theorem not_all_derivations_vanish_on_polynomial_coordinate
    [Nontrivial T] (i : σ) :
    ¬ ∀ d : Derivation R T T,
      d (algebraMap (MvPolynomial σ R) T (MvPolynomial.X i)) = 0 := by
  intro h
  have hz := h (polynomialCoordinateDerivation R T σ i)
  rw [polynomialCoordinateDerivation_X] at hz
  exact one_ne_zero hz

end PolynomialCoordinates

section PolynomialPresentations

variable (σ : Type v)

/-- Transport a polynomial partial derivation through an algebra
equivalence, with values in the target algebra. -/
noncomputable def polynomialCoordinateDerivationOnAlgebra
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) : Derivation R S T :=
  Derivation.mk'
    (((Algebra.linearMap S T).restrictScalars R).comp
      (e.toLinearMap.comp
        ((MvPolynomial.pderiv i).toLinearMap.comp e.symm.toLinearMap)))
    (by
      intro a b
      change algebraMap S T (e (MvPolynomial.pderiv i (e.symm (a * b)))) =
        a • algebraMap S T (e (MvPolynomial.pderiv i (e.symm b))) +
        b • algebraMap S T (e (MvPolynomial.pderiv i (e.symm a)))
      rw [map_mul, (MvPolynomial.pderiv i).leibniz]
      simp [Algebra.smul_def])

theorem polynomialCoordinateDerivationOnAlgebra_X
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) :
    polynomialCoordinateDerivationOnAlgebra R S T σ e i
      (e (MvPolynomial.X i)) = 1 := by
  change algebraMap S T
      (e (MvPolynomial.pderiv i (e.symm (e (MvPolynomial.X i))))) = 1
  simp

/-- Extend a transported polynomial coordinate derivation through the
formally etale map from the presented algebra to its target. -/
noncomputable def polynomialCoordinateDerivationViaEquiv
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) : Derivation R T T :=
  extendDerivationFormallyEtale R S T
    (polynomialCoordinateDerivationOnAlgebra R S T σ e i)

theorem polynomialCoordinateDerivationViaEquiv_X
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) :
    polynomialCoordinateDerivationViaEquiv R S T σ e i
      (algebraMap S T (e (MvPolynomial.X i))) = 1 := by
  rw [polynomialCoordinateDerivationViaEquiv,
    extendDerivationFormallyEtale_algebraMap,
    polynomialCoordinateDerivationOnAlgebra_X]

end PolynomialPresentations

end CriticalDepth
