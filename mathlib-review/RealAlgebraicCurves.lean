import RealAlgebraicImage
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Curves in real polynomial zero loci

A polynomial derivation preserving an ideal defines an ordinary differential
equation. Its integral curve starting in the zero locus stays there locally
because the evaluated ideal generators satisfy a homogeneous linear system.
-/

open Filter Set
open scoped BigOperators Topology NNReal

noncomputable section

namespace CriticalDepth.RealAlgebraicImage

variable {σ : Type*}

/-- The common real zeros of the polynomials in an ideal. -/
def polynomialZeroLocus (I : Ideal (MvPolynomial σ ℝ)) : Set (σ → ℝ) :=
  {x | ∀ f ∈ I, MvPolynomial.aeval x f = 0}

section FiniteCoordinates

variable [Fintype σ]

theorem contDiff_polynomial_eval (f : MvPolynomial σ ℝ) :
    ContDiff ℝ 1 (fun x : σ → ℝ => MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
      using (contDiff_const : ContDiff ℝ 1 (fun _ : σ → ℝ => c))
  | add p q hp hq =>
    simpa only [map_add, Pi.add_apply] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.aeval_X, Pi.mul_apply]
      using hp.mul (contDiff_apply ℝ (fun _ : σ => ℝ) i)

/-- A finite homogeneous linear system with continuous coefficients and
zero initial state has the zero solution locally. -/
theorem eventually_eq_zero_of_hasDerivAt_eq_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {y : ℝ → E}
    (hA : ContinuousAt A 0)
    (hy : ∀ᶠ t in 𝓝 0, HasDerivAt y (A t (y t)) t)
    (hy₀ : y 0 = 0) :
    y =ᶠ[𝓝 0] (fun _ => 0) := by
  let K : ℝ≥0 := ‖A 0‖₊ + 1
  have hbound : ∀ᶠ t in 𝓝 0, ‖A t‖₊ < K :=
    hA.nnnorm.eventually_lt continuousAt_const (by
      change ‖A 0‖₊ < ‖A 0‖₊ + 1
      exact lt_add_of_pos_right _ zero_lt_one)
  apply ODE_solution_unique_of_eventually
    (v := fun t z => A t z) (s := fun _ => Set.univ) (K := K)
  · filter_upwards [hbound] with t ht
    exact ((A t).lipschitzWith.weaken ht.le).lipschitzOnWith
  · exact hy.mono fun t ht => ⟨ht, Set.mem_univ _⟩
  · exact Filter.Eventually.of_forall fun t =>
      ⟨by simpa only [map_zero] using (hasDerivAt_const t (0 : E)), Set.mem_univ _⟩
  · exact hy₀

/-- A point of a derivation-invariant ideal lies on a local integral curve
that stays in the same zero locus. -/
theorem exists_integral_curve_in_zeroLocus
    (I : Ideal (MvPolynomial σ ℝ)) (x : σ → ℝ) (hx : x ∈ polynomialZeroLocus I)
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))
    (hD : ∀ f ∈ I, D f ∈ I) :
    ∃ γ : ℝ → (σ → ℝ), γ 0 = x ∧ ContDiffAt ℝ 1 γ 0 ∧
      (∀ᶠ t in 𝓝 0, γ t ∈ polynomialZeroLocus I) ∧
      ∀ᶠ t in 𝓝 0, HasDerivAt γ (fun i => MvPolynomial.aeval (γ t) (D (MvPolynomial.X i))) t := by
  classical
  let v : (σ → ℝ) → σ → ℝ := fun x i => MvPolynomial.aeval x (D (MvPolynomial.X i))
  have hv : ContDiff ℝ 1 v :=
    contDiff_pi.mpr fun i => contDiff_polynomial_eval (D (MvPolynomial.X i))
  obtain ⟨γ, hγ₀, ε, hε, hγ⟩ :=
    hv.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := x) 0
  have hε₀ : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by simp [hε]
  have hNhd : Ioo (0 - ε) (0 + ε) ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds hε₀
  have hDeriv : ∀ᶠ t in 𝓝 0, HasDerivAt γ (v (γ t)) t := Filter.mem_of_superset hNhd hγ
  have hγcont : ContinuousOn γ (Ioo (0 - ε) (0 + ε)) :=
    fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hC1 : ContDiffAt ℝ 1 γ 0 := by
    refine contDiffAt_one_iff.mpr
      ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)), _, hNhd, ?_, ?_⟩
    · exact ((ContinuousLinearMap.smulRightL ℝ ℝ (σ → ℝ) 1).continuous.comp_continuousOn
        (hv.continuous.comp_continuousOn hγcont))
    · intro t ht
      exact (hγ t ht).hasFDerivAt
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing I)
  have hgSpan : Ideal.span (Set.range g) = I := hg
  have hgI (i : Fin n) : g i ∈ I := hgSpan ▸ Ideal.mem_span_range_self
  have hcoeff : ∀ i : Fin n, ∃ c : Fin n → MvPolynomial σ ℝ, ∑ j, c j * g j = D (g i) := by
    intro i
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [hgSpan]
    exact hD _ (hgI i)
  choose c hc using hcoeff
  let y : ℝ → Fin n → ℝ := fun t i => MvPolynomial.aeval (γ t) (g i)
  let B (i j : Fin n) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i).comp
      (ContinuousLinearMap.proj j)
  let A (t : ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ∑ i, ∑ j, MvPolynomial.aeval (γ t) (c i j) • B i j
  have hA (t : ℝ) (z : Fin n → ℝ) (i : Fin n) :
      A t z i = ∑ j, MvPolynomial.aeval (γ t) (c i j) * z j := by
    simp [A, B, Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  have hAcont : ContinuousAt A 0 := by
    change ContinuousAt (fun t => ∑ i, ∑ j, MvPolynomial.aeval (γ t) (c i j) • B i j) 0
    apply ContinuousOn.continuousAt _ hNhd
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((contDiff_polynomial_eval (c i j)).continuous.comp_continuousOn hγcont).smul
      continuousOn_const
  have hy : ∀ᶠ t in 𝓝 0, HasDerivAt y (A t (y t)) t := by
    filter_upwards [hDeriv] with t ht
    apply hasDerivAt_pi.mpr
    intro i
    have hyi := hasDerivAt_aeval_of_coordinate_velocities D (hasDerivAt_pi.mp ht) (g i)
    have hval : MvPolynomial.aeval (γ t) (D (g i)) = A t (y t) i := by
      rw [← hc i, map_sum, hA]
      simp [y]
    simpa only [hval] using hyi
  have hy₀ : y 0 = 0 := by
    funext i
    change MvPolynomial.aeval (γ 0) (g i) = 0
    rw [hγ₀]
    exact hx _ (hgI i)
  have hyZero := eventually_eq_zero_of_hasDerivAt_eq_linear hAcont hy hy₀
  refine ⟨γ, hγ₀, hC1, ?_, hDeriv⟩
  filter_upwards [hyZero] with t ht
  intro f hf
  have hspan : I ≤ RingHom.ker (MvPolynomial.aeval (γ t)).toRingHom := by
    rw [← hgSpan]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (congrFun ht i)
  exact RingHom.mem_ker.mp (hspan hf)

end FiniteCoordinates

section InfiniteEvaluations

variable [Fintype σ]

private theorem exists_polynomialDerivation_at_infinite_image
    (S : Set (σ → ℝ)) (f : MvPolynomial σ ℝ)
    (hinf : (Set.range fun x : S => MvPolynomial.aeval x.val f).Infinite) :
    ∃ (p : Ideal (MvPolynomial σ ℝ)), vanishingIdeal S ≤ p ∧
      ∃ (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (x : S),
        (∀ u ∈ p, D u ∈ p) ∧ x.val ∈ polynomialZeroLocus p ∧
          MvPolynomial.aeval x.val (D f) ≠ 0 := by
  classical
  let ev : S → MvPolynomial σ ℝ →ₐ[ℝ] ℝ := fun x => MvPolynomial.aeval x.val
  let I := vanishingIdeal S
  have hI (x : S) : I ≤ RingHom.ker (ev x).toRingHom :=
    iInf_le (fun x : S => RingHom.ker (ev x).toRingHom) x
  have hex : ∃ p ∈ I.minimalPrimes, (evaluationValuesAbove ev p f).Infinite := by
    by_contra! hfinite
    have hAll := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).biUnion hfinite
    apply hinf
    refine hAll.subset ?_
    rintro _ ⟨x, rfl⟩
    let : (RingHom.ker (ev x).toRingHom).IsPrime := RingHom.ker_isPrime _
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (hI x)
    exact Set.mem_biUnion hp ⟨x, hpx, rfl⟩
  obtain ⟨p, hp, hpinfinite⟩ := hex
  let : p.IsPrime := hp.isPrime
  let K := FractionRing (MvPolynomial σ ℝ ⧸ p)
  let : CharZero K := ⟨by
    intro m n hmn
    have hReal : (m : ℝ) = (n : ℝ) :=
      (algebraMap ℝ K).injective (by simpa only [map_natCast] using hmn)
    exact Nat.cast_injective hReal⟩
  have hField : ∃ D : Derivation ℝ K K,
      D (quotientFractionMap ℝ (MvPolynomial σ ℝ) p f) ≠ 0 := by
    by_contra! hzero
    exact hpinfinite (finite_evaluationValuesAbove_of_isAlgebraic ev p f
      (isAlgebraic_of_forall_derivation_eq_zero ℝ K _ hzero))
  obtain ⟨D, hD⟩ := hField
  obtain ⟨E, hE, hEf⟩ := exists_polynomialDerivation_preserving_prime p f D hD
  let Q := {q : Ideal (MvPolynomial σ ℝ) | q ∈ I.minimalPrimes ∧ q ≠ p}
  have hQfinite : Q.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset (fun _ hq => hq.1)
  let : Fintype Q := hQfinite.fintype
  have hwitness : ∀ q : Q, ∃ b : MvPolynomial σ ℝ, b ∈ q.val ∧ b ∉ p := by
    intro q
    by_contra! hall
    have hle : q.val ≤ p := fun _ hb => hall _ hb
    exact q.property.2 (le_antisymm hle (hp.2 q.property.1.1 hle))
  choose b hb hbp using hwitness
  let z := ∏ q : Q, b q
  have hz : z ∉ p := by
    intro hmem
    obtain ⟨q, _, hq⟩ := (Ideal.IsPrime.prod_mem_iff (p := p)).mp hmem
    exact hbp q hq
  have hExists : ∃ x : S, ev x (E f * z) ≠ 0 := by
    by_contra! hall
    exact (hp.isPrime.mul_notMem hEf hz) (hp.le ((mem_vanishingIdeal_iff S).mpr hall))
  obtain ⟨x, hx⟩ := hExists
  let : (RingHom.ker (ev x).toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (hI x)
  have hqeq : q = p := by
    by_contra hne
    let i : Q := ⟨q, hq, hne⟩
    have hbi : ev x (b i) = 0 := RingHom.mem_ker.mp (hqx (hb i))
    have hz0 : ev x z = 0 := by
      change ev x (∏ j : Q, b j) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hbi
    exact hx (by rw [map_mul, hz0, mul_zero])
  have hpx : p ≤ RingHom.ker (ev x).toRingHom := hqeq ▸ hqx
  refine ⟨p, hp.le, E, x, hE, ?_, ?_⟩
  · exact fun u hu => RingHom.mem_ker.mp (hpx hu)
  · intro hzero
    exact hx (by rw [map_mul, show ev x (E f) = 0 from hzero, zero_mul])

/-- Infinite values of a polynomial on a real algebraic set yield a local
smooth curve along which that polynomial has a nonzero derivative. -/
theorem exists_curve_of_infinite_polynomial_values
    (I : Ideal (MvPolynomial σ ℝ)) (f : MvPolynomial σ ℝ)
    (hinf : (Set.range fun x : polynomialZeroLocus I => MvPolynomial.aeval x.val f).Infinite) :
    ∃ γ : ℝ → (σ → ℝ), ContDiffAt ℝ 1 γ 0 ∧
      (∀ᶠ t in 𝓝 0, γ t ∈ polynomialZeroLocus I) ∧
      ∃ v : ℝ, v ≠ 0 ∧ HasDerivAt (fun t => MvPolynomial.aeval (γ t) f) v 0 := by
  obtain ⟨p, hp, D, x, hD, hxp, hmove⟩ :=
    exists_polynomialDerivation_at_infinite_image (polynomialZeroLocus I) f hinf
  obtain ⟨γ, hγ₀, hC1, hStay, hγ⟩ := exists_integral_curve_in_zeroLocus p x.val hxp D hD
  have hIp : I ≤ p := le_trans
    (fun g hg => (mem_vanishingIdeal_iff (polynomialZeroLocus I)).mpr
      (fun y => y.property g hg)) hp
  refine ⟨γ, hC1, hStay.mono (fun t ht g hg => ht g (hIp hg)), ?_⟩
  have hγAt := mem_of_mem_nhds hγ
  have hImage := hasDerivAt_aeval_of_coordinate_velocities D (hasDerivAt_pi.mp hγAt) f
  exact ⟨MvPolynomial.aeval (γ 0) (D f), by rwa [hγ₀], hImage⟩

end InfiniteEvaluations

end CriticalDepth.RealAlgebraicImage
