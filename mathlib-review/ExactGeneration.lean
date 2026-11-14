import NativeLogicalCurves
import DenseUnitaryAdjointSpan
import UnitaryCurveProducts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Exact generation at a common depth budget. -/

noncomputable section

namespace CriticalDepth.ReviewV2

open CriticalDepth.Manuscript Unitary
open Filter Set
open scoped Topology Matrix.Norms.Frobenius

private def phase {K : ℕ} (t : ℝ) : U K :=
  unitaryRotation (1 : M K) (by simp) (by simp) t

private theorem phase_val {K : ℕ} (t : ℝ) :
    (phase (K := K) t).val =
      ((Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) • (1 : M K) := by
  change rotation (1 : M K) t = _
  simp [rotation, affine, add_smul]

private theorem phase_mk {K : ℕ} (t : ℝ) :
    projectiveMk (ι := Fin K) (phase t) = 1 := by
  rw [← map_one (projectiveMk (ι := Fin K))]
  apply (projectiveMk_eq_iff (Fin K) _ 1).mpr
  change ∃ z : ℂ, star z * z = 1 ∧ (phase (K := K) t).val = z • (1 : M K)
  refine ⟨_, ?_, phase_val t⟩
  have h : ((Circle.exp t : Circle) : ℂ) =
      (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I, mul_comm Complex.I]
  rw [← h]
  exact circle_star_mul_self (Circle.exp t)

private theorem phase_smooth (K : ℕ) :
    ContDiffAt ℝ 1 (fun t => (phase (K := K) t).val) 0 := by
  simp only [phase_val]
  have hcos : ContDiff ℝ 1 (fun t => (Real.cos t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have hsin : ContDiff ℝ 1 (fun t => (Real.sin t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  exact ((hcos.add (contDiff_const.mul hsin)).smul contDiff_const).contDiffAt

private theorem phase_deriv (K : ℕ) :
    HasDerivAt (fun t => (phase (K := K) t).val) (Complex.I • (1 : M K)) 0 := by
  simp only [phase_val]
  have hcos := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_cos 0)
  have hsin := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_sin 0)
  have ha : HasDerivAt (fun t : ℝ =>
      (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) Complex.I 0 := by
    simpa [Function.comp_def, Pi.add_apply, Complex.ofRealCLM_apply] using
      hcos.fun_add (hsin.const_mul Complex.I)
  exact ha.smul_const (1 : M K)

private theorem generated_eq_top_of_curve {K : ℕ} (G : Subgroup (PU (Fin K)))
    (hG : G.topologicalClosure = ⊤) (c : ℝ → U K)
    (h0 : c 0 = 1) (hmem : ∀ t, projectiveMk (ι := Fin K) (c t) ∈ G)
    (hC : ContDiffAt ℝ 1 (fun t => (c t).val) 0) (X : M K)
    (hX : HasDerivAt (fun t => (c t).val) X 0)
    (hnonscalar : ¬ ∃ z : ℂ, X = z • (1 : M K)) : G = ⊤ := by
  classical
  let H := G.comap (projectiveMk (ι := Fin K))
  have hdense : Dense (G : Set (PU (Fin K))) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hG]
    rfl
  have hHdense : Dense (H : Set (U K)) :=
    QuotientGroup.isOpenQuotientMap_mk.dense_preimage_iff.mpr hdense
  obtain ⟨m, V, hspan⟩ := UnitaryAdjointSpan.exists_fin_conjugates_spanning_skewAdjoint
    X (skew_of_unitary_derivative h0 hX) hnonscalar H hHdense
  let curves : Option (Fin m) → ℝ → U K
    | none => phase
    | some i => fun t => (V i).val * c t * (V i).val⁻¹
  let tangents : Option (Fin m) → M K
    | none => Complex.I • (1 : M K)
    | some i => UnitaryAdjointSpan.conj (V i).val X
  apply UnitaryCurveProducts.projective_eq_top_of_unitaryCurveProducts G hG
    curves ?_ ?_ ?_ tangents ?_ ?_
  · intro i
    cases i <;> simp [curves, h0, phase, unitaryRotation]
  · intro i t
    cases i with
    | none => rw [show curves none t = phase t from rfl, phase_mk]; exact G.one_mem
    | some i =>
      change curves (some i) t ∈ H
      exact H.mul_mem (H.mul_mem (V i).property (hmem t)) (H.inv_mem (V i).property)
  · intro i
    cases i with
    | none => exact phase_smooth K
    | some i => exact (contDiffAt_const.mul hC).mul contDiffAt_const
  · intro i
    cases i with
    | none => exact phase_deriv K
    | some i =>
      change HasDerivAt (fun t : ℝ => (V i).val.val * (c t).val * ((V i).val⁻¹).val)
        (UnitaryAdjointSpan.conj (V i).val X) 0
      rw [show UnitaryAdjointSpan.conj (V i).val X =
        (V i).val.val * X * ((V i).val⁻¹).val from rfl]
      exact (hX.const_mul (V i).val.val).mul_const (((V i).val⁻¹).val)
  · change skewAdjoint.submodule ℝ (M K) ≤ Submodule.span ℝ (Set.range tangents)
    rw [← hspan]
    apply Submodule.span_mono
    rintro _ (heq | ⟨i, rfl⟩)
    · exact ⟨none, heq.symm⟩
    · exact ⟨some i, rfl⟩


/-- Theorem 2(2) of the manuscript. All depths use the same native gate
alphabet and exact subsystem encoding. -/
theorem nativeExactDepth_eq_max {n K g : ℕ} {dim : Fin n → ℕ}
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (hV : V.conjTranspose * V = 1) (hK : 2 ≤ K) (hg : 1 ≤ g)
    (q : ℕ) :
    nativeExactDepth V q = max (nativeCriticalDepth V q) (nativeDenseDepth V q) := by
  apply nativeExactDepth_eq_max_of_identity_neighborhood V q hK
  intro h _ hi hDense
  obtain ⟨c, X, h0, hmem, hC, hX, hnonscalar⟩ :=
    exists_native_curve_of_infinite_image ⟨V, hV⟩ hK hg q h hi
  rw [generated_eq_top_of_curve _ hDense c h0 hmem hC X hX hnonscalar]
  exact Filter.univ_mem


example :
    nativeExactDepth FourQubit.encoding 2 =
      max (nativeCriticalDepth FourQubit.encoding 2) (nativeDenseDepth FourQubit.encoding 2) :=
  nativeExactDepth_eq_max FourQubit.encoding FourQubit.encoding_isometry (by decide) (by decide) 2

#print nativeExactDepth_eq_max
#print axioms nativeExactDepth_eq_max

end CriticalDepth.ReviewV2
