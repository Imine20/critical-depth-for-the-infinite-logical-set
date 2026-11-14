import CriticalDepthMathlib
import Mathlib.RingTheory.FiniteType
import Mathlib.Data.Set.Card

namespace CriticalDepth.Manuscript20261114

/-- The joint scalar evaluations are indexed by the minimal-prime components. -/
theorem evaluationImage_encard_le_minimalPrimes {R : Type*}
    [CommRing R] [Algebra ℂ R] {ι : Type*} (r : ι → R)
    (h : ∀ i, ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∀ D : Derivation ℂ (FractionRing (R ⧸ p)) (FractionRing (R ⧸ p)),
        D (quotientFractionMap ℂ R p (r i)) = 0) :
    (Set.range fun f : R →ₐ[ℂ] ℂ => fun i => f (r i)).encard ≤
      ((⊥ : Ideal R).minimalPrimes).encard := by
  classical
  let P := (⊥ : Ideal R).minimalPrimes
  have hscalar (p : P) (i : ι) :
      ∃ c : ℂ, r i - algebraMap ℂ R c ∈ p.val := by
    letI : p.val.IsPrime := p.property.isPrime
    let K := FractionRing (R ⧸ p.val)
    letI : CharZero K := ⟨by
      intro m n hmn
      have heq : (m : ℂ) = (n : ℂ) :=
        (algebraMap ℂ K).injective (by simpa only [map_natCast] using hmn)
      exact Nat.cast_injective heq⟩
    obtain ⟨c, hc⟩ := exists_scalar_mod_kernel_of_forall_derivation_eq_zero
      ℂ K R (quotientFractionMap ℂ R p.val) (r i) (h i p.val p.property)
    rw [quotientFractionMap_ker ℂ R p.val] at hc
    exact ⟨c, hc⟩
  let constants (p : P) (i : ι) : ℂ := Classical.choose (hscalar p i)
  have hsubset : (Set.range fun f : R →ₐ[ℂ] ℂ => fun i => f (r i)) ⊆
      constants '' (Set.univ : Set P) := by
    rintro _ ⟨f, rfl⟩
    letI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
    obtain ⟨p, hp, hle⟩ := Ideal.exists_minimalPrimes_le
      (bot_le : (⊥ : Ideal R) ≤ RingHom.ker f.toRingHom)
    refine ⟨⟨p, hp⟩, Set.mem_univ _, ?_⟩
    funext i
    have hzero := hle (Classical.choose_spec (hscalar ⟨p, hp⟩ i))
    change f (r i - algebraMap ℂ R (constants ⟨p, hp⟩ i)) = 0 at hzero
    rw [map_sub, f.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at hzero
    exact hzero.symm
  calc
    _ ≤ (constants '' (Set.univ : Set P)).encard := Set.encard_le_encard hsubset
    _ ≤ (Set.univ : Set P).encard := Set.encard_image_le constants _
    _ = _ := Set.encard_univ P

/-- Supplemental Lemma S1 for a finitely generated complex coordinate algebra. -/
theorem finiteEvaluationImage {R : Type*} [CommRing R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] {ι : Type*} [Fintype ι] (r : ι → R)
    (h : ∀ i, ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∀ D : Derivation ℂ (FractionRing (R ⧸ p)) (FractionRing (R ⧸ p)),
        D (quotientFractionMap ℂ R p (r i)) = 0) :
    (Set.range fun f : R →ₐ[ℂ] ℂ => fun i => f (r i)).Finite := by
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  exact evaluation_image_finite_of_minimalPrime_derivations ℂ R r h

/-- The scalar algebra is a nonempty test case with a genuine evaluation. -/
theorem finiteEvaluationImage_scalarCall :
    (Set.range fun f : ℂ →ₐ[ℂ] ℂ => fun i : Fin 2 =>
      f (algebraMap ℂ ℂ (if i = 0 then 1 else 2))).Finite := by
  apply finiteEvaluationImage
  intro i p hp D
  simpa only [AlgHom.commutes] using D.map_algebraMap (if i = 0 then (1 : ℂ) else 2)

#print axioms evaluationImage_encard_le_minimalPrimes
#print axioms finiteEvaluationImage
#print axioms finiteEvaluationImage_scalarCall
#print axioms CriticalDepth.ReviewV2.HilbertCircuitTransport.theoremOne_arbitrary_carriers

end CriticalDepth.Manuscript20261114
