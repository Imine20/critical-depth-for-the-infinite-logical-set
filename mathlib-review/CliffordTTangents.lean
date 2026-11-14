import CliffordTWords
import CliffordTClosureCriterion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Tangent directions for the Clifford–T rotation circles
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

/-- The four real coordinates of the skew-Hermitian 2 × 2 matrices. -/
def pauliTangent (a b c d : ℝ) : QubitOperator :=
  Complex.I • ((d : ℂ) • (1 : QubitOperator) + pauliCombination a b c)

theorem pauliTangent_as_linearCombination (a b c d : ℝ) :
    pauliTangent a b c d =
      d • (Complex.I • (1 : QubitOperator)) +
      a • (Complex.I • SinglePauli.X.matrix) +
      b • (Complex.I • SinglePauli.Y.matrix) +
      c • (Complex.I • SinglePauli.Z.matrix) := by
  ext i j
  simp [pauliTangent, pauliCombination, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- The logical Pauli matrices and the identity span the real tangent
space once multiplied by i. -/
theorem skewAdjoint_eq_pauliTangent (A : QubitOperator)
    (hA : A ∈ skewAdjoint.submodule ℝ QubitOperator) :
    ∃ a b c d : ℝ, A = pauliTangent a b c d := by
  have hs : A.conjTranspose = -A := hA
  have h00 := congrArg (fun M : QubitOperator => M 0 0) hs
  have h11 := congrArg (fun M : QubitOperator => M 1 1) hs
  have h01 := congrArg (fun M : QubitOperator => M 0 1) hs
  change star (A 0 0) = - A 0 0 at h00
  change star (A 1 1) = - A 1 1 at h11
  change star (A 1 0) = - A 0 1 at h01
  have r00 : (A 0 0).re = 0 := by
    have h := congrArg Complex.re h00
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  have r11 : (A 1 1).re = 0 := by
    have h := congrArg Complex.re h11
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  have r01 : (A 1 0).re = -(A 0 1).re := by
    have h := congrArg Complex.re h01
    simpa only [Complex.star_def, Complex.conj_re, Complex.neg_re] using h
  have i01 : (A 1 0).im = (A 0 1).im := by
    have h := congrArg Complex.im h01
    simpa only [Complex.star_def, Complex.conj_im, Complex.neg_im, neg_inj] using h
  refine ⟨(A 0 1).im, (A 0 1).re, ((A 0 0).im - (A 1 1).im) / 2,
    ((A 0 0).im + (A 1 1).im) / 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauliTangent, pauliCombination, SinglePauli.matrix, Matrix.one_apply,
      smul_eq_mul, Complex.mul_re, Complex.mul_im, r00, r11, r01, i01] <;> ring

/-- Three successive quarter-turn images of a Pauli direction span all
traceless tangents when the horizontal and vertical parts are nonzero. -/
theorem skewAdjoint_le_span_of_pauliTangent_quarter_turns {a b c : ℝ}
    (hHoriz : a ^ 2 + b ^ 2 ≠ 0) (hVert : c ≠ 0) :
    skewAdjoint.submodule ℝ QubitOperator ≤
      Submodule.span ℝ ({pauliTangent 0 0 0 1, pauliTangent a b c 0,
        pauliTangent b (-a) c 0, pauliTangent (-a) (-b) c 0} : Set QubitOperator) := by
  classical
  let T := Submodule.span ℝ ({pauliTangent 0 0 0 1, pauliTangent a b c 0,
    pauliTangent b (-a) c 0, pauliTangent (-a) (-b) c 0} : Set QubitOperator)
  have h0 : pauliTangent 0 0 0 1 ∈ T := Submodule.subset_span (by simp)
  have h1 : pauliTangent a b c 0 ∈ T := Submodule.subset_span (by simp)
  have h2 : pauliTangent b (-a) c 0 ∈ T := Submodule.subset_span (by simp)
  have h3 : pauliTangent (-a) (-b) c 0 ∈ T := Submodule.subset_span (by simp)
  intro A hA
  obtain ⟨x, y, z, d, hAeq⟩ := skewAdjoint_eq_pauliTangent A hA
  let s := (a * x + b * y) / (a ^ 2 + b ^ 2)
  let t := (b * x - a * y) / (a ^ 2 + b ^ 2)
  let r := (z / c - s - t) / 2
  have hx : (s + r) * a + t * b + r * (-a) = x := by
    dsimp only [s, t]
    field_simp
    ring
  have hy : (s + r) * b + t * (-a) + r * (-b) = y := by
    dsimp only [s, t]
    field_simp
    ring
  have hz : (s + r) * c + t * c + r * c = z := by
    dsimp only [r]
    field_simp
    ring
  have hEq : A = d • pauliTangent 0 0 0 1 + (s + r) • pauliTangent a b c 0 +
      t • pauliTangent b (-a) c 0 + r • pauliTangent (-a) (-b) c 0 := by
    rw [hAeq]
    simp only [pauliTangent_as_linearCombination, zero_smul, one_smul, add_zero, zero_add]
    simp only [smul_add, smul_smul]
    have hsum : (s + r) * c + t * c + r * c = z := hz
    rw [← hx, ← hy, ← hsum]
    simp only [add_smul]
    abel
  rw [hEq]
  exact T.add_mem (T.add_mem (T.add_mem (T.smul_mem _ h0) (T.smul_mem _ h1))
    (T.smul_mem _ h2)) (T.smul_mem _ h3)

/-- Rotation curves have real tangent iP at zero. -/
theorem rotation_hasDerivAt_zero (P : QubitOperator) :
    HasDerivAt (rotation P) (Complex.I • P) 0 := by
  have hcos := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_cos 0)
  have hsin := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_sin 0)
  have hcos' : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using hcos
  have hsin' : HasDerivAt (fun t : ℝ => Complex.I * (Real.sin t : ℂ)) Complex.I 0 := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using hsin.const_mul Complex.I
  have h := (hcos'.smul_const (1 : QubitOperator)).fun_add (hsin'.smul_const P)
  rw [zero_smul, zero_add] at h
  exact h

theorem rotation_contDiffAt_zero (P : QubitOperator) :
    ContDiffAt ℝ 1 (rotation P) 0 := by
  have hcos : ContDiff ℝ 1 (fun t => (Real.cos t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have hsin : ContDiff ℝ 1 (fun t => (Real.sin t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  exact ((hcos.smul contDiff_const).add
    ((contDiff_const.mul hsin).smul contDiff_const)).contDiffAt

#print axioms skewAdjoint_eq_pauliTangent
#print axioms skewAdjoint_le_span_of_pauliTangent_quarter_turns
#print axioms rotation_hasDerivAt_zero

end

end CriticalDepth.Manuscript20261114.CliffordT
