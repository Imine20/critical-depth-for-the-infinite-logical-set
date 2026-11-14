import FaultVariationalTrace
import Mathlib.Analysis.Matrix.Order

/-!
Trace norm, including the Hermitian dilation used for arbitrary inputs.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def matrixTraceNorm (A : Matrix ι ι ℂ) : ℝ :=
  (CFC.abs A).trace.re

theorem matrixTraceNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ matrixTraceNorm A :=
  (Complex.nonneg_iff.mp (CFC.abs_nonneg A).posSemidef.trace_nonneg).1

theorem trace_submatrix_equiv_same (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    (A.submatrix e e).trace = A.trace :=
  Fintype.sum_equiv e _ _ fun _ => rfl

theorem matrixTraceNorm_submatrix_equiv (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    matrixTraceNorm (A.submatrix e e) = matrixTraceNorm A := by
  have h :
      CFC.abs (A.submatrix e e) = (CFC.abs A).submatrix e e := by
    unfold CFC.abs
    apply CFC.sqrt_unique
    · have hs := CFC.abs_mul_abs A
      rw [Matrix.star_eq_conjTranspose] at hs
      change (CFC.abs A).submatrix e e * (CFC.abs A).submatrix e e =
        (A.submatrix e e).conjTranspose * A.submatrix e e
      rw [Matrix.submatrix_mul_equiv _ _ e e e, hs,
        Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ e e e]
    · exact ((CFC.abs_nonneg A).posSemidef.submatrix e).nonneg
  rw [matrixTraceNorm, h, trace_submatrix_equiv_same]
  rfl

theorem matrixTraceNorm_eq_hermitianTraceNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    matrixTraceNorm A = hermitianTraceNorm A hA := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  have hu : U.conjTranspose * U = 1 := (Unitary.mem_iff.mp hA.eigenvectorUnitary.property).1
  unfold matrixTraceNorm hermitianTraceNorm
  rw [CFC.abs_eq_cfc_norm A hA.isSelfAdjoint, hA.cfc_eq]
  change (U * Matrix.diagonal (fun i => ((‖hA.eigenvalues i‖ : ℝ) : ℂ)) * U.conjTranspose).trace.re = _
  rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, Matrix.trace_diagonal]
  simp [Real.norm_eq_abs]

theorem matrixTraceNorm_star (A : Matrix ι ι ℂ) :
    matrixTraceNorm A.conjTranspose = matrixTraceNorm A := by
  have h₁ := (Matrix.posSemidef_self_mul_conjTranspose A).isHermitian
  have h₂ := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have hc : (A * A.conjTranspose).charpoly = (A.conjTranspose * A).charpoly :=
    Matrix.charpoly_mul_comm _ _
  have hs (X : Matrix ι ι ℂ) (hx : X.PosSemidef) :
      (CFC.sqrt X).trace.re = ∑ i, Real.sqrt (hx.1.eigenvalues i) := by
    let U : Matrix ι ι ℂ := hx.1.eigenvectorUnitary
    have hu : U.conjTranspose * U = 1 := (Unitary.mem_iff.mp hx.1.eigenvectorUnitary.property).1
    rw [CFC.sqrt_eq_real_sqrt X hx.nonneg,
      cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn Real.sqrt_zero, hx.1.cfc_eq]
    change (U * Matrix.diagonal (fun i => (Real.sqrt (hx.1.eigenvalues i) : ℂ)) *
      U.conjTranspose).trace.re = _
    rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, Matrix.trace_diagonal]
    simp
  unfold matrixTraceNorm CFC.abs
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  rw [hs _ (Matrix.posSemidef_self_mul_conjTranspose A),
    hs _ (Matrix.posSemidef_conjTranspose_mul_self A)]
  have hr := congrArg (fun p : Polynomial ℂ =>
    (p.roots.map (Real.sqrt ∘ Complex.re)).sum) hc
  rw [h₁.roots_charpoly_eq_eigenvalues, h₂.roots_charpoly_eq_eigenvalues] at hr
  simpa only [Multiset.map_map, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, ← Finset.sum_eq_multiset_sum] using hr

def hermitianDilation (A : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 A A.conjTranspose 0

theorem hermitianDilation_isHermitian (A : Matrix ι ι ℂ) :
    (hermitianDilation A).IsHermitian := by
  unfold hermitianDilation
  exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero

theorem matrixTraceNorm_hermitianDilation (A : Matrix ι ι ℂ) :
    matrixTraceNorm (hermitianDilation A) = 2 * matrixTraceNorm A := by
  let X := CFC.abs A.conjTranspose
  let Y := CFC.abs A
  let D : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := Matrix.fromBlocks X 0 0 Y
  have hx : X.PosSemidef := (CFC.abs_nonneg _).posSemidef
  have hy : Y.PosSemidef := (CFC.abs_nonneg _).posSemidef
  have hd : D.PosSemidef := by
    obtain ⟨Bx, hBx⟩ := posSemidef_factor_conjTranspose X hx
    obtain ⟨By, hBy⟩ := posSemidef_factor_conjTranspose Y hy
    have hFactor :
        (Matrix.fromBlocks Bx 0 0 By) * (Matrix.fromBlocks Bx 0 0 By).conjTranspose = D := by
      simp [D, hBx, hBy, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    exact hFactor ▸ Matrix.posSemidef_self_mul_conjTranspose _
  have hD : CFC.abs (hermitianDilation A) = D := by
    unfold CFC.abs
    apply CFC.sqrt_unique _ hd.nonneg
    rw [Matrix.star_eq_conjTranspose, (hermitianDilation_isHermitian A).eq]
    have hX : X * X = A * A.conjTranspose := by
      simpa only [X, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
        CFC.abs_mul_abs A.conjTranspose
    have hY : Y * Y = A.conjTranspose * A := CFC.abs_mul_abs A
    simp [D, hermitianDilation, Matrix.fromBlocks_multiply, hX, hY]
  rw [matrixTraceNorm, hD]
  change ((∑ i : ι ⊕ ι, D i i).re) = _
  rw [Fintype.sum_sum_type, Complex.add_re]
  change matrixTraceNorm A.conjTranspose + matrixTraceNorm A = _
  rw [matrixTraceNorm_star, two_mul]

#print axioms matrixTraceNorm_eq_hermitianTraceNorm
#print axioms matrixTraceNorm_hermitianDilation

end
end CriticalDepth.FaultChannelEffects
