import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import CriticalDepth.DerivationExtension

/-!
# Differential constants in characteristic-zero field extensions

The principal statement says that an element annihilated by every base-linear
derivation of a characteristic-zero field extension is algebraic over the
base field. The argument includes a purported transcendental element in a
transcendence basis and extends its polynomial partial derivation through
localization and the separable algebraic extension. The extension mechanism
is developed in `CriticalDepth.DerivationExtension`.

The preceding differential-structure lemmas also record finite-dimensional
extension and uniqueness. No finite-generation hypothesis on the ambient
field is used in the principal statement. In particular,
`Algebra.FiniteType` on the final field is not used as a substitute for
finite generation as a field extension.
-/

namespace CriticalDepth

universe u v w

/-- The differential structure whose derivation is identically zero. -/
def zeroDifferential (R : Type u) [CommRing R] : Differential R :=
  ⟨0⟩

/-- Compatibility of a differential structure with a constant base field. -/
def CompatibleWithZero
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (d : Differential K) : Prop :=
  letI : Differential F := zeroDifferential F
  letI : Differential K := d
  DifferentialAlgebra F K

/-- An element is constant for every derivation extending the zero
derivation of the base field. -/
def IsDifferentialConstant
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (x : K) : Prop :=
  ∀ d : Differential K,
    CompatibleWithZero F K d → @Differential.deriv K _ d x = 0

theorem zeroDifferential_compatible
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K] :
    CompatibleWithZero F K (zeroDifferential K) := by
  letI : Differential F := zeroDifferential F
  letI : Differential K := zeroDifferential K
  change DifferentialAlgebra F K
  refine ⟨?_⟩
  intro a
  change (0 : K) = algebraMap F K (0 : F)
  exact (map_zero (algebraMap F K)).symm

/-- Every scalar from the base field is a differential constant. -/
theorem isDifferentialConstant_algebraMap
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (a : F) :
    IsDifferentialConstant F K (algebraMap F K a) := by
  intro d h
  letI : Differential F := zeroDifferential F
  letI : Differential K := d
  letI : DifferentialAlgebra F K := h
  change Differential.deriv (algebraMap F K a) = 0
  rw [DifferentialAlgebra.deriv_algebraMap]
  change algebraMap F K (0 : F) = 0
  exact map_zero (algebraMap F K)

/-- A differential structure extends across a finite-dimensional extension of
characteristic-zero fields. This is the actual existence statement used by
the proposed differential-constants argument. -/
theorem exists_compatible_differential
    (F : Type u) (K : Type v)
    [Field F] [Differential F] [CharZero F]
    [Field K] [Algebra F K] [FiniteDimensional F K] :
    ∃ d : Differential K, letI := d; DifferentialAlgebra F K := by
  refine ⟨Differential.differentialFiniteDimensional F K, ?_⟩
  exact Differential.differentialAlgebraFiniteDimensional (F := F) (K := K)

/-- Finite-dimensional extensions of a constant characteristic-zero field
have no nonzero compatible derivation. This is the algebraic direction of
the intended differential-constants criterion. -/
theorem isDifferentialConstant_of_finiteDimensional
    (F : Type u) (K : Type v)
    [Field F] [CharZero F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (x : K) :
    IsDifferentialConstant F K x := by
  intro d h
  letI : Differential F := zeroDifferential F
  letI : Unique {e : Differential K // CompatibleWithZero F K e} :=
    Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := K)
  have heq :
      (⟨d, h⟩ : {e : Differential K // CompatibleWithZero F K e}) =
        ⟨zeroDifferential K, zeroDifferential_compatible F K⟩ :=
    Subsingleton.elim _ _
  have hd : d = zeroDifferential K := congrArg Subtype.val heq
  rw [hd]
  rfl

section DerivationConstants

open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [CharZero K] [Algebra F K]

/-- A transcendence-basis polynomial algebra maps formally etale to the
ambient characteristic-zero field: first localize to its field of
fractions, then use the separable algebraic extension. -/
theorem formallyEtale_adjoin_of_transcendenceBasis
    {ι : Type w} (b : ι → K) (hb : IsTranscendenceBasis F b) :
    Algebra.FormallyEtale (Algebra.adjoin F (Set.range b)) K := by
  let S := Algebra.adjoin F (Set.range b)
  let L := IntermediateField.adjoin F (Set.range b)
  letI : Algebra S L := by
    change Algebra (Algebra.adjoin F (Set.range b))
      (IntermediateField.adjoin F (Set.range b))
    infer_instance
  letI : IsScalarTower S L K := by
    change IsScalarTower (Algebra.adjoin F (Set.range b))
      (IntermediateField.adjoin F (Set.range b)) K
    infer_instance
  letI : IsFractionRing S L := by
    change IsFractionRing (Algebra.adjoin F (Set.range b))
      (IntermediateField.adjoin F (Set.range b))
    infer_instance
  letI : Algebra.IsAlgebraic L K := hb.isAlgebraic_field
  letI : Algebra.IsSeparable L K := inferInstance
  letI : Algebra.FormallyEtale L K :=
    Algebra.FormallyEtale.of_isSeparable L K
  letI : Algebra.FormallyEtale S L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors S)
  exact Algebra.FormallyEtale.comp S L K

/-- In characteristic zero, an element annihilated by every base-linear
derivation is algebraic over the base field. No finite-generation
hypothesis on the ambient field is required. -/
theorem isAlgebraic_of_forall_derivation_eq_zero
    (a : K) (h : ∀ d : Derivation F K K, d a = 0) :
    IsAlgebraic F a := by
  classical
  by_contra ha
  have htrans : Transcendental F a := ha
  have hsingle : AlgebraicIndepOn F id ({a} : Set K) := by
    letI : Subsingleton ({a} : Set K) := ⟨by
      intro x y
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp x.property).trans
        (Set.mem_singleton_iff.mp y.property).symm⟩
    change AlgebraicIndependent F (Subtype.val : ({a} : Set K) → K)
    exact (algebraicIndependent_singleton_iff
      (R := F) (x := (Subtype.val : ({a} : Set K) → K))
      (⟨a, by simp⟩ : ({a} : Set K))).2 htrans
  obtain ⟨t, hst, hb⟩ := exists_isTranscendenceBasis_superset hsingle
  let i : t := ⟨a, hst (by simp)⟩
  let b : t → K := Subtype.val
  let S := Algebra.adjoin F (Set.range b)
  let e : MvPolynomial t F ≃ₐ[F] S := hb.1.aevalEquiv
  letI : Algebra.FormallyEtale S K :=
    formallyEtale_adjoin_of_transcendenceBasis F K b hb
  let d : Derivation F K K :=
    polynomialCoordinateDerivationViaEquiv F S K t e i
  have hcoord : algebraMap S K (e (MvPolynomial.X i)) = a := by
    change algebraMap S K (hb.1.aevalEquiv (MvPolynomial.X i)) = a
    rw [hb.1.algebraMap_aevalEquiv]
    simp [i]
  have hdi : d (algebraMap S K (e (MvPolynomial.X i))) = 1 :=
    polynomialCoordinateDerivationViaEquiv_X F S K t e i
  rw [hcoord] at hdi
  exact one_ne_zero (hdi.symm.trans (h d))

end DerivationConstants

end CriticalDepth
