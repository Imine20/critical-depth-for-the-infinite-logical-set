import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integrality from scalar values on prime components

If an element agrees with a base scalar modulo every minimal prime of a
Noetherian algebra, a product of the corresponding linear polynomials has
nilpotent value at that element. A power of that monic polynomial is an
annihilating polynomial. Nilpotents in the coordinate algebra are therefore
allowed; no reducedness assumption is imposed.
-/

namespace CriticalDepth

open Polynomial

universe u v

/-- Scalar values modulo the finitely many minimal prime components give
an integral element. The scalar witness may depend on the component. -/
theorem isIntegral_of_scalar_mod_minimalPrimes
    (F : Type u) (R : Type v)
    [Field F] [CommRing R] [Algebra F R] [IsNoetherianRing R]
    (r : R)
    (h : ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∃ c : F, r - algebraMap F R c ∈ p) :
    IsIntegral F r := by
  classical
  let primes := (⊥ : Ideal R).minimalPrimes
  have hfinite : primes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R (⊥ : Ideal R)
  let ps : Finset (Ideal R) := hfinite.toFinset
  let c : Ideal R → F := fun p =>
    if hp : p ∈ primes then Classical.choose (h p hp) else 0
  have hc (p : Ideal R) (hp : p ∈ primes) :
      r - algebraMap F R (c p) ∈ p := by
    simpa only [c, dif_pos hp] using Classical.choose_spec (h p hp)
  let P : F[X] := ∏ p ∈ ps, (X - C (c p))
  have hmonic_aux (s : Finset (Ideal R)) :
      (∏ p ∈ s, (X - C (c p)) : F[X]).Monic := by
    induction s using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
        rw [Finset.prod_insert hps]
        exact (monic_X_sub_C (c p)).mul ih
  have hmonic : P.Monic := hmonic_aux ps
  have hmem (p : Ideal R) (hp : p ∈ primes) : aeval r P ∈ p := by
    have hp_ps : p ∈ ps := by simpa [ps] using hp
    have hprod (s : Finset (Ideal R)) :
        p ∈ s → (∏ q ∈ s, (r - algebraMap F R (c q))) ∈ p := by
      induction s using Finset.induction with
      | empty => intro hps; simp at hps
      | @insert q s hqs ih =>
          intro hps
          rw [Finset.prod_insert hqs]
          rcases Finset.mem_insert.mp hps with hpq | hps
          · subst q
            exact p.mul_mem_right _ (hc p hp)
          · exact p.mul_mem_left _ (ih hps)
    simpa only [P, map_prod, map_sub, aeval_X, aeval_C] using hprod ps hp_ps
  have hrad : aeval r P ∈ (⊥ : Ideal R).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Ideal.mem_sInf.mpr hmem
  change ∃ N : ℕ, (aeval r P) ^ N ∈ (⊥ : Ideal R) at hrad
  obtain ⟨N, hN⟩ := hrad
  have hzero : (aeval r P) ^ N = 0 := by simpa using hN
  refine ⟨P ^ N, hmonic.pow N, ?_⟩
  change aeval r (P ^ N) = 0
  rw [map_pow]
  exact hzero

end CriticalDepth
