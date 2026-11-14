import CriticalDepthMathlib
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.RingTheory.Localization.Integer

/-!
# Evaluations on minimal components of a real algebraic set

The coordinate ring uses the ideal of all polynomials vanishing on the real
witness set. This makes real evaluations jointly faithful. The results here
locate a minimal component with an algebraic tangent direction that changes
an observed coordinate. Integrating that direction to a real curve is a
separate step.
-/

noncomputable section

namespace CriticalDepth.RealAlgebraicImage

open scoped BigOperators

section EvaluationAlgebra

variable {A : Type*} [CommRing A] [Algebra ℝ A] {ι : Type*}
variable (ev : ι → A →ₐ[ℝ] ℝ)

/-- A real point on a specified minimal component detects each nonzero
element of that component, if the given evaluations detect elements of the
original ring. -/
theorem exists_eval_above_minimalPrime_ne_zero [IsNoetherianRing A]
    (hsep : ∀ a : A, (∀ x, ev x a = 0) → a = 0)
    {p : Ideal A} (hp : p ∈ minimalPrimes A) {a : A} (ha : a ∉ p) :
    ∃ x : ι, p ≤ RingHom.ker (ev x).toRingHom ∧ ev x a ≠ 0 := by
  classical
  let : p.IsPrime := hp.isPrime
  let Q := {q : Ideal A | q ∈ minimalPrimes A ∧ q ≠ p}
  have hQfinite : Q.Finite :=
    (minimalPrimes.finite_of_isNoetherianRing (R := A)).subset (fun _ hq => hq.1)
  let : Fintype Q := hQfinite.fintype
  have hwitness : ∀ q : Q, ∃ b : A, b ∈ q.val ∧ b ∉ p := by
    intro q
    by_contra! h
    have hle : q.val ≤ p := fun _ hb => h _ hb
    exact q.property.2 (le_antisymm hle (hp.2 q.property.1.1 hle))
  choose b hb hbp using hwitness
  let z := ∏ q : Q, b q
  have hz : z ∉ p := by
    intro hmem
    obtain ⟨q, _, hq⟩ := (Ideal.IsPrime.prod_mem_iff (p := p)).mp hmem
    exact hbp q hq
  have haz : a * z ≠ 0 := by
    intro hzero
    exact (hp.isPrime.mul_notMem ha hz) (by rw [hzero]; exact p.zero_mem)
  obtain ⟨x, hx⟩ : ∃ x : ι, ev x (a * z) ≠ 0 := by
    by_contra! hall
    exact haz (hsep _ hall)
  let : (RingHom.ker (ev x).toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal A) ≤ RingHom.ker (ev x).toRingHom)
  have hqeq : q = p := by
    by_contra hne
    let i : Q := ⟨q, hq, hne⟩
    have hbi : ev x (b i) = 0 := RingHom.mem_ker.mp (hqx (hb i))
    have hz0 : ev x z = 0 := by
      change ev x (∏ j : Q, b j) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hbi
    exact hx (by rw [map_mul, hz0, mul_zero])
  refine ⟨x, hqeq ▸ hqx, ?_⟩
  intro ha0
  exact hx (by rw [map_mul, ha0, zero_mul])

/-- Values of a coordinate at the selected evaluations on a component. -/
def evaluationValuesAbove (p : Ideal A) (a : A) : Set ℝ :=
  {y | ∃ x : ι, p ≤ RingHom.ker (ev x).toRingHom ∧ ev x a = y}

theorem finite_evaluationValuesAbove_of_isAlgebraic
    (p : Ideal A) [p.IsPrime] (a : A)
    (ha : IsAlgebraic ℝ (quotientFractionMap ℝ A p a)) :
    (evaluationValuesAbove ev p a).Finite := by
  obtain ⟨f, hf, hroot⟩ := ha
  refine (Polynomial.finite_setOfPred_isRoot hf).subset ?_
  rintro y ⟨x, hpx, rfl⟩
  have hmk : Polynomial.aeval (Ideal.Quotient.mk p a) f = 0 := by
    apply IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))
    let ψ := IsScalarTower.toAlgHom ℝ (A ⧸ p) (FractionRing (A ⧸ p))
    change ψ (Polynomial.aeval (Ideal.Quotient.mk p a) f) = ψ 0
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact hroot
  let ex := Ideal.Quotient.liftₐ p (ev x) (fun b hb => RingHom.mem_ker.mp (hpx hb))
  have hEx : ex (Ideal.Quotient.mk p a) = ev x a := rfl
  have hEval : Polynomial.aeval (ev x a) f = 0 := by
    rw [← hEx, Polynomial.aeval_algHom_apply ex, hmk, map_zero]
  change Polynomial.IsRoot f (ev x a)
  simpa only [Polynomial.IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self,
    Polynomial.eval₂_id] using hEval

/-- A coordinate taking infinitely many real values is transcendental on
some minimal component, so a real-linear field derivation moves it. -/
theorem exists_minimalPrime_derivation_of_infinite_values [IsNoetherianRing A]
    (a : A) (hinf : (Set.range fun x : ι => ev x a).Infinite) :
    ∃ (p : Ideal A) (_hp : p ∈ minimalPrimes A),
      ∃ D : Derivation ℝ (FractionRing (A ⧸ p)) (FractionRing (A ⧸ p)),
        D (quotientFractionMap ℝ A p a) ≠ 0 := by
  classical
  by_contra! hconstant
  have hfinite : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hAll := hfinite.biUnion (t := fun p => evaluationValuesAbove ev p a) (by
    intro p hp
    let : p.IsPrime := hp.isPrime
    let K := FractionRing (A ⧸ p)
    let : CharZero K := ⟨by
      intro m n hmn
      have hReal : (m : ℝ) = (n : ℝ) :=
        (algebraMap ℝ K).injective (by simpa only [map_natCast] using hmn)
      exact Nat.cast_injective hReal⟩
    exact finite_evaluationValuesAbove_of_isAlgebraic ev p a
      (isAlgebraic_of_forall_derivation_eq_zero ℝ K _ (hconstant p hp)))
  apply hinf
  refine hAll.subset ?_
  rintro _ ⟨x, rfl⟩
  let : (RingHom.ker (ev x).toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal A) ≤ RingHom.ker (ev x).toRingHom)
  exact Set.mem_biUnion hp ⟨x, hpx, rfl⟩

end EvaluationAlgebra

section PolynomialEvaluations

variable {σ : Type*} (S : Set (σ → ℝ))

/-- Polynomials vanishing at every point of the real point set. -/
def vanishingIdeal : Ideal (MvPolynomial σ ℝ) :=
  ⨅ x : S, RingHom.ker (MvPolynomial.aeval x.val).toRingHom

theorem mem_vanishingIdeal_iff {f : MvPolynomial σ ℝ} :
    f ∈ vanishingIdeal S ↔ ∀ x : S, MvPolynomial.aeval x.val f = 0 := by
  simp [vanishingIdeal]

/-- The coordinate algebra formed from the real point set itself. -/
abbrev CoordinateRing :=
  MvPolynomial σ ℝ ⧸ vanishingIdeal S

/-- Evaluation at one of the points defining the vanishing ideal. -/
def coordinateEvaluation (x : S) : CoordinateRing S →ₐ[ℝ] ℝ :=
  Ideal.Quotient.liftₐ (vanishingIdeal S)
    (MvPolynomial.aeval x.val)
    (fun f hf => (mem_vanishingIdeal_iff S).mp hf x)

theorem coordinateEvaluations_separate (a : CoordinateRing S)
    (ha : ∀ x, coordinateEvaluation S x a = 0) : a = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (mem_vanishingIdeal_iff S).mpr (fun x => show MvPolynomial.aeval x.val f = 0 from ha x)

end PolynomialEvaluations

section PolynomialDerivations

variable {σ : Type*} [Finite σ]

/-- Clearing the denominators on the finitely many variables gives a polynomial
derivation preserving the prime ideal, with the same nonvanishing test. -/
theorem exists_polynomialDerivation_preserving_prime
    (p : Ideal (MvPolynomial σ ℝ)) [p.IsPrime] (f : MvPolynomial σ ℝ)
    (D : Derivation ℝ (FractionRing (MvPolynomial σ ℝ ⧸ p))
      (FractionRing (MvPolynomial σ ℝ ⧸ p)))
    (hD : D (quotientFractionMap ℝ (MvPolynomial σ ℝ) p f) ≠ 0) :
    ∃ E : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ),
      (∀ u ∈ p, E u ∈ p) ∧ E f ∉ p := by
  classical
  let P := MvPolynomial σ ℝ
  let A := P ⧸ p
  let K := FractionRing A
  let φ := quotientFractionMap ℝ P p
  obtain ⟨denom, hDenom⟩ := IsLocalization.exist_integer_multiples_of_finite
    (M := nonZeroDivisors A) (fun i : σ => D (φ (MvPolynomial.X i)))
  have hNumerator : ∀ i : σ, ∃ v : P,
      φ v = algebraMap A K (denom : A) * D (φ (MvPolynomial.X i)) := by
    intro i
    obtain ⟨a, ha⟩ := hDenom i
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨v, ?_⟩
    change algebraMap A K (Ideal.Quotient.mk p v) =
      algebraMap A K (denom : A) * D (φ (MvPolynomial.X i))
    simpa only [Algebra.smul_def] using ha
  choose v hv using hNumerator
  let E : Derivation ℝ P P := MvPolynomial.mkDerivation ℝ v
  have hIdentity (u : P) :
      φ (E u) = algebraMap A K (denom : A) * D (φ u) := by
    induction u using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.derivation_C, map_zero]
      have hc : φ (MvPolynomial.C c) = algebraMap ℝ K c := φ.commutes c
      rw [hc, Derivation.map_algebraMap, mul_zero]
    | add u w hu hw =>
      rw [map_add, map_add, hu, hw, map_add, map_add, mul_add]
    | mul_X u i hu =>
      rw [E.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        hu, show E (MvPolynomial.X i) = v i from MvPolynomial.mkDerivation_X ℝ v i,
        hv, map_mul, D.leibniz, smul_eq_mul, smul_eq_mul]
      ring
  have hKer : RingHom.ker φ.toRingHom = p := quotientFractionMap_ker ℝ P p
  have hzero (u : P) : φ u = 0 ↔ u ∈ p := by
    exact RingHom.mem_ker.symm.trans (congrArg (fun I : Ideal P => u ∈ I) hKer).to_iff
  refine ⟨E, ?_, ?_⟩
  · intro u hu
    apply (hzero _).mp
    rw [hIdentity, (hzero u).mpr hu, map_zero, mul_zero]
  · intro hEf
    have hDenom_ne : algebraMap A K (denom : A) ≠ 0 := by
      intro hzero
      exact (mem_nonZeroDivisors_iff_ne_zero.mp denom.property)
        (IsFractionRing.injective A K (by rw [map_zero]; exact hzero))
    exact (mul_ne_zero hDenom_ne hD)
      ((hIdentity f).symm.trans ((hzero _).mpr hEf))

end PolynomialDerivations

section PolynomialCurves

variable {σ : Type*}

/-- Evaluating a polynomial along an integral curve differentiates the
polynomial by the derivation defining the coordinate velocities. -/
theorem hasDerivAt_aeval_of_coordinate_velocities
    (E : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))
    {γ : ℝ → σ → ℝ} {t₀ : ℝ}
    (hγ : ∀ i, HasDerivAt (fun t => γ t i)
      (MvPolynomial.aeval (γ t₀) (E (MvPolynomial.X i))) t₀)
    (f : MvPolynomial σ ℝ) :
    HasDerivAt (fun t => MvPolynomial.aeval (γ t) f)
      (MvPolynomial.aeval (γ t₀) (E f)) t₀ := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      MvPolynomial.derivation_C, map_zero] using (hasDerivAt_const t₀ c)
  | add p q hp hq =>
    simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp =>
    rw [E.leibniz]
    simp only [smul_eq_mul, map_mul, map_add, MvPolynomial.aeval_X]
    simpa only [mul_comm (γ t₀ i), add_comm] using hp.fun_mul (hγ i)

end PolynomialCurves

end CriticalDepth.RealAlgebraicImage
