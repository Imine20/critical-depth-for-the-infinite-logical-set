import CircuitRealPolynomial
import RealAlgebraicCurves
import GenerationThresholds
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed

/-! Smooth logical unitary curves extracted from the real circuit equations. -/

noncomputable section

namespace CriticalDepth.ReviewV2

open CriticalDepth.Manuscript CriticalDepth.CircuitRealPolynomial
open CriticalDepth.RealAlgebraicImage
open Filter Set
open scoped Topology Matrix.Norms.Frobenius

abbrev U (K : ℕ) := Matrix.unitaryGroup (Fin K) ℂ
abbrev M (K : ℕ) := Matrix (Fin K) (Fin K) ℂ

private def entry {K : ℕ} (i j : Fin K) : M K →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem skew_of_unitary_derivative {K : ℕ} {u : ℝ → U K} {X : M K}
    (h0 : u 0 = 1) (hX : HasDerivAt (fun t => (u t).val) X 0) :
    star X = -X := by
  have h : HasDerivAt (fun t => star (u t).val * (u t).val)
      (star X * (u 0).val + star (u 0).val * X) 0 := hX.star.fun_mul hX
  have hc : HasDerivAt (fun t => star (u t).val * (u t).val) (0 : M K) 0 := by
    have heq : (fun t => star (u t).val * (u t).val) = (fun _ : ℝ => (1 : M K)) :=
      funext fun t => (u t).property.1
    rw [heq]
    exact hasDerivAt_const (0 : ℝ) (1 : M K)
  have hsum : star X + X = 0 := by
    simpa [h0] using h.unique hc
  exact eq_neg_of_add_eq_zero_left hsum

private def logicalEntryMap {n r K g : ℕ} {dim : Fin n → ℕ}
    (s : GateIndex n r → Finset (Fin n)) :
    (Variables (dim := dim) s K g → ℝ) →L[ℝ] M K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j =>
        ⟨x (Sum.inr (Sum.inl (i,j)), false), x (Sum.inr (Sum.inl (i,j)), true)⟩
      map_add' := by intro x y; ext i j <;> rfl
      map_smul' := by
        intro a x
        ext i j
        change Complex.mk _ _ = a • Complex.mk _ _
        apply Complex.ext <;> simp [Pi.smul_apply, RCLike.smul_re, RCLike.smul_im, smul_eq_mul] }

private theorem logicalEntryMap_apply {n r K g : ℕ} {dim : Fin n → ℕ}
    (s : GateIndex n r → Finset (Fin n)) (x : Variables (dim := dim) s K g → ℝ) :
    logicalEntryMap (dim := dim) s x = (logical (dim := dim) s).map (evaluation x) := by
  ext i j
  change Complex.mk _ _ = evaluation x (logical (dim := dim) s i j)
  exact (evaluation_variable x (Sum.inr (Sum.inl (i,j)))).symm

private theorem aeval_eq_eval {σ : Type*} (x : σ → ℝ) (f : MvPolynomial σ ℝ) :
    MvPolynomial.aeval x f = MvPolynomial.eval x f := by
  simp only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]

/-- Infinite native alphabets give a locally smooth projective motion whose
lift has a nonscalar tangent at the identity. -/
theorem exists_native_curve_of_infinite_image {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g) (q h : ℕ)
    (hi : (nativeLogicalImage C.encoding q h).Infinite) :
    ∃ c : ℝ → U K, ∃ X : M K, c 0 = 1 ∧
      (∀ t, projectiveMk (ι := Fin K) (c t) ∈ generatedLogicalSubgroup C.encoding q h) ∧
      ContDiffAt ℝ 1 (fun t => (c t).val) 0 ∧
      HasDerivAt (fun t => (c t).val) X 0 ∧
      ¬ ∃ z : ℂ, X = z • (1 : M K) := by
  classical
  obtain ⟨r, s, hs, a, b, part, hinf⟩ :=
    infinite_observable_of_infinite_image C hK hg q h hi
  let I := witnessIdeal s C.encoding
  let f := if part then (observable (dim := dim) (g := g) s a b).im else (observable (dim := dim) (g := g) s a b).re
  have hInf : (Set.range fun x : polynomialZeroLocus I =>
      MvPolynomial.aeval x.val f).Infinite := by
    apply hinf.mono
    rintro y ⟨x, rfl⟩
    have hx : x.val ∈ polynomialZeroLocus I := by
      intro p hp
      rw [aeval_eq_eval]
      exact x.property p hp
    exact ⟨⟨x, hx⟩, aeval_eq_eval x.val f⟩
  obtain ⟨γ, hγ, hmem, v, hv, hcoord⟩ :=
    exists_curve_of_infinite_polynomial_values I f hInf
  have hmatrix (t : ℝ) (ht : γ t ∈ polynomialZeroLocus I) :
      ∃ W : U K, W.val = logicalEntryMap (dim := dim) s (γ t) ∧
        projectiveMk (ι := Fin K) W ∈ nativeLogicalImage C.encoding q h := by
    rw [logicalEntryMap_apply]
    apply witness_gate_mem s C q h (Nat.le_of_lt_succ r.isLt) hs
    intro p hp
    rw [← aeval_eq_eval]
    exact ht p hp
  have hzero : γ 0 ∈ polynomialZeroLocus I := mem_of_mem_nhds (s := {t : ℝ | γ t ∈ polynomialZeroLocus I}) hmem
  let u : ℝ → U K := fun t =>
    if ht : γ t ∈ polynomialZeroLocus I then Classical.choose (hmatrix t ht) else
      Classical.choose (hmatrix 0 hzero)
  have hu (t : ℝ) : projectiveMk (ι := Fin K) (u t) ∈ nativeLogicalImage C.encoding q h := by
    unfold u
    split
    · rename_i ht
      exact (Classical.choose_spec (hmatrix t ht)).2
    · exact (Classical.choose_spec (hmatrix 0 hzero)).2
  have huEq : (fun t => (u t).val) =ᶠ[𝓝 0] fun t => logicalEntryMap (dim := dim) s (γ t) := by
    filter_upwards [hmem] with t ht
    simpa only [u, dif_pos ht] using (Classical.choose_spec (hmatrix t ht)).1
  have huC : ContDiffAt ℝ 1 (fun t => (u t).val) 0 :=
    ((logicalEntryMap (dim := dim) s).contDiff.contDiffAt.comp 0 hγ).congr_of_eventuallyEq huEq
  let Y := deriv (fun t => (u t).val) 0
  have hY : HasDerivAt (fun t => (u t).val) Y 0 :=
    (huC.differentiableAt (by decide)).hasDerivAt
  let c : ℝ → U K := fun t => u t * (u 0)⁻¹
  have hc0 : c 0 = 1 := mul_inv_cancel _
  have cMem (t : ℝ) :
      projectiveMk (ι := Fin K) (c t) ∈ generatedLogicalSubgroup C.encoding q h := by
    change _ ∈ Subgroup.closure (nativeLogicalImage C.encoding q h)
    simp only [c, _root_.map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (hu t))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (hu 0)))
  let X := Y * ((u 0)⁻¹).val
  have hcD : HasDerivAt (fun t => (c t).val) X 0 := hY.mul_const _
  refine ⟨c, X, hc0, cMem, huC.mul contDiffAt_const, hcD, ?_⟩
  rintro ⟨z, hz⟩
  have hYscalar : Y = z • (u 0).val := by
    calc
      Y = X * (u 0).val := by
        change Y = (Y * star (u 0).val) * (u 0).val
        rw [mul_assoc, (u 0).property.1, mul_one]
      _ = z • (u 0).val := by rw [hz, smul_mul_assoc, one_mul]
  have hObs : HasDerivAt (fun t => MvPolynomial.aeval (γ t) f) 0 0 := by
    let W := (u 0).val
    have hvanish : ∀ i j k l : Fin K,
        Y i k * (star W) l j + W i k * (star Y) l j = 0 := by
      intro i j k l
      have hskew := skew_of_unitary_derivative hc0 hcD
      have hstar : star z = -z := by
        have hentry := congrFun (congrFun hskew a.1) a.1
        simpa [hz, star_smul, Matrix.smul_apply, Matrix.one_apply] using hentry
      simp [hYscalar, W, hstar, Matrix.smul_apply, smul_eq_mul] <;> ring
    have h₁ : HasDerivAt (fun t => (u t).val a.1 b.1) (Y a.1 b.1) 0 :=
      (entry a.1 b.1).hasFDerivAt.comp_hasDerivAt 0 hY
    have h₂ : HasDerivAt (fun t => (star (u t).val) b.2 a.2) ((star Y) b.2 a.2) 0 :=
      (entry b.2 a.2).hasFDerivAt.comp_hasDerivAt 0 hY.star
    have hprod : HasDerivAt (fun t => conjugationCoordinates (u t).val a b) 0 0 := by
      rw [← hvanish a.1 a.2 b.1 b.2]
      exact h₁.fun_mul h₂
    cases hpart : part
    · apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hprod).congr_of_eventuallyEq
      filter_upwards [huEq] with t ht
      change MvPolynomial.aeval (γ t) f = (conjugationCoordinates (u t).val a b).re
      rw [aeval_eq_eval, ht, logicalEntryMap_apply, ← evaluation_observable]
      simp [f, hpart]
    · apply (Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hprod).congr_of_eventuallyEq
      filter_upwards [huEq] with t ht
      change MvPolynomial.aeval (γ t) f = (conjugationCoordinates (u t).val a b).im
      rw [aeval_eq_eval, ht, logicalEntryMap_apply, ← evaluation_observable]
      simp [f, hpart]
  exact hv (hcoord.unique hObs)

#print axioms exists_native_curve_of_infinite_image

end CriticalDepth.ReviewV2
