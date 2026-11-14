import UnitaryCurveProducts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Spanning the skew-adjoint matrices by Pauli tangents
-/

open scoped BigOperators Matrix.Norms.Frobenius

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2

noncomputable section

private theorem skewPart_complex_smul_of_selfAdjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P : Operator ι) (hP : star P = P) (z : ℂ) :
    (skewAdjointPart ℝ (z • P) : Operator ι) = z.im • (Complex.I • P) := by
  rw [skewAdjointPart_apply_coe, star_smul, hP, ← sub_smul]
  ext i j
  change (((⅟2 : ℝ) : ℂ) * ((z - star z) * P i j)) =
    (z.im : ℂ) * (Complex.I * P i j)
  have hz : z - star z = 2 * (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [hz, invOf_eq_inv]
  push_cast
  ring

/-- The real span of the derivatives of the tensor Pauli rotations at the
identity is the full skew-adjoint tangent space. -/
theorem skewAdjoint_le_span_tensorPauliTangents (k : ℕ) :
    skewAdjoint.submodule ℝ (Operator (QubitBasis k)) ≤
      Submodule.span ℝ (Set.range fun p : Fin k → SinglePauli =>
        Complex.I • pauliMatrix 0 p) := by
  intro A hA
  have hP : A ∈ Submodule.span ℂ (Set.range fun p : Fin k → SinglePauli =>
      pauliMatrix 0 p) := by rw [unphased_pauliMatrix_span_eq_top]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hP
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨fun p => (c p).im, ?_⟩
  let project : Operator (QubitBasis k) →ₗ[ℝ] Operator (QubitBasis k) :=
    (skewAdjoint.submodule ℝ (Operator (QubitBasis k))).subtype.comp (skewAdjointPart ℝ)
  have h := congrArg project hc
  rw [map_sum] at h
  have hterm (p : Fin k → SinglePauli) :
      project (c p • pauliMatrix 0 p) = (c p).im • (Complex.I • pauliMatrix 0 p) :=
    skewPart_complex_smul_of_selfAdjoint _ (unphased_pauliMatrix_selfAdjoint p) (c p)
  have hA' : project A = A := by
    change (skewAdjointPart ℝ A : Operator (QubitBasis k)) = A
    change star A = -A at hA
    rw [skewAdjointPart_apply_coe, hA, sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]
  simpa only [hterm, hA'] using h

private theorem rotation_has_generator_derivative {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P : Operator ι) :
    HasDerivAt (rotation P) (Complex.I • P) 0 := by
  have hcos := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_cos 0)
  have hsin := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_sin 0)
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using hcos
  have hs : HasDerivAt (fun t : ℝ => Complex.I * (Real.sin t : ℂ)) Complex.I 0 := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using hsin.const_mul Complex.I
  have h := (hc.smul_const (1 : Operator ι)).fun_add (hs.smul_const P)
  rw [zero_smul, zero_add] at h
  exact h

private theorem rotation_contDiffAt_identity {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P : Operator ι) :
    ContDiffAt ℝ 1 (rotation P) 0 := by
  have hcos : ContDiff ℝ 1 (fun t => (Real.cos t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have hsin : ContDiff ℝ 1 (fun t => (Real.sin t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  exact ((hcos.smul contDiff_const).add
    ((contDiff_const.mul hsin).smul contDiff_const)).contDiffAt

/-- The ordinary exponential rotation of an unphased tensor Pauli. -/
def tensorPauliRotation {k : ℕ} (p : Fin k → SinglePauli) (t : ℝ) :
    Matrix.unitaryGroup (QubitBasis k) ℂ :=
  unitaryRotation (pauliMatrix 0 p) (unphased_pauliMatrix_selfAdjoint p)
    (unphased_pauliMatrix_sq p) t

/-- Containing the one-parameter groups of all tensor Paulis forces a
projective subgroup to be open. -/
theorem isOpen_of_contains_tensorPauliRotations {k : ℕ} (G : Subgroup (PU (QubitBasis k)))
    (h : ∀ (p : Fin k → SinglePauli) (t : ℝ),
      projectiveMk (QubitBasis k) (tensorPauliRotation p t) ∈ G) :
    IsOpen (G : Set (PU (QubitBasis k))) := by
  let U := G.comap (projectiveMk (QubitBasis k))
  have hN := UnitaryCurveProducts.one_nhds_of_unitaryCurveProducts U
    tensorPauliRotation (fun p => Subtype.ext (rotation_zero (pauliMatrix 0 p))) h
    (fun p => rotation_contDiffAt_identity (pauliMatrix 0 p))
    (fun p => Complex.I • pauliMatrix 0 p)
    (fun p => rotation_has_generator_derivative (pauliMatrix 0 p))
    (skewAdjoint_le_span_tensorPauliTangents k)
  have hOpenMap : IsOpenMap (projectiveMk (QubitBasis k)) := QuotientGroup.isOpenMap_coe
  have hImage := hOpenMap.image_mem_nhds hN
  rw [map_one] at hImage
  apply G.isOpen_of_mem_nhds
  apply Filter.mem_of_superset hImage
  rintro u ⟨v, hv, rfl⟩
  exact hv

#print axioms skewAdjoint_le_span_tensorPauliTangents
#print axioms isOpen_of_contains_tensorPauliRotations

end

end CriticalDepth.Manuscript20261114
