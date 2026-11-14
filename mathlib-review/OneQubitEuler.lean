import CriticalDepthMathlib
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Exact Euler decomposition of a one-qubit projective unitary

A determinant-one matrix is determined by its first row. Its two complex
entries give the magnitudes and phases in a three-rotation ZXZ product.
A scalar phase handles the determinant of an arbitrary unitary.
-/

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114.OneQubitEuler

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix

noncomputable section

private theorem xSelf : star (SinglePauli.X.matrix : Operator (Fin 2)) =
    SinglePauli.X.matrix := singlePauli_selfAdjoint .X

private theorem zSelf : star (SinglePauli.Z.matrix : Operator (Fin 2)) =
    SinglePauli.Z.matrix := singlePauli_selfAdjoint .Z

private theorem xSquare : SinglePauli.X.matrix * SinglePauli.X.matrix = 1 :=
  singlePauli_sq .X

private theorem zSquare : SinglePauli.Z.matrix * SinglePauli.Z.matrix = 1 :=
  singlePauli_sq .Z

/-- Arbitrary-angle X and Z rotations in the named logical Pauli basis. -/
def projectiveX (t : ℝ) : PU (Fin 2) :=
  projectiveRotation SinglePauli.X.matrix xSelf xSquare t

def projectiveZ (t : ℝ) : PU (Fin 2) :=
  projectiveRotation SinglePauli.Z.matrix zSelf zSquare t

private def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem star_phase (t : ℝ) : star (phase t) = phase (-t) := by
  unfold phase
  change starRingEnd ℂ (Complex.exp ((t : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj]
  simp

private theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I t

private theorem phase_unit (t : ℝ) : star (phase t) * phase t = 1 := by
  rw [star_phase, ← phase_add, neg_add_cancel]
  simp [phase]

private theorem star_ofReal (r : ℝ) : star (r : ℂ) = r := Complex.conj_ofReal r

private theorem star_I : star Complex.I = -Complex.I := Complex.conj_I

private theorem rotationZ_diagonal (t : ℝ) :
    rotation SinglePauli.Z.matrix t =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then phase t else phase (-t)) := by
  have hphase (s : ℝ) : phase s = (Real.cos s : ℂ) + (Real.sin s : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I s
  simp only [hphase, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, affine, SinglePauli.matrix, smul_eq_mul] <;> ring

private theorem rotationX_entries (t : ℝ) :
    rotation SinglePauli.X.matrix t = !![(Real.cos t : ℂ), Complex.I * (Real.sin t : ℂ);
                                        Complex.I * (Real.sin t : ℂ), (Real.cos t : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, affine, SinglePauli.matrix, Matrix.one_apply, smul_eq_mul]

private theorem rotation_zxz_entries (s t u : ℝ) :
    rotation SinglePauli.Z.matrix s * rotation SinglePauli.X.matrix t *
      rotation SinglePauli.Z.matrix u =
      !![(Real.cos t : ℂ) * phase (s + u), (Complex.I * (Real.sin t : ℂ)) * phase (s - u);
        (Complex.I * (Real.sin t : ℂ)) * phase (-(s - u)), (Real.cos t : ℂ) * phase (-(s + u))] := by
  ext i j
  rw [rotationZ_diagonal, rotationZ_diagonal, rotationX_entries, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [sub_eq_add_neg, neg_add_rev, phase_add, mul_assoc, mul_left_comm, mul_comm]

/-- A determinant-one unitary has the standard two-entry SU(2) form. -/
theorem unitary_det_one_eq_entries (U : Operator (Fin 2))
    (hu : IsUnitary U) (hdet : U.det = 1) :
    U = !![U 0 0, U 0 1; -star (U 0 1), star (U 0 0)] := by
  let A : Operator (Fin 2) := !![U 1 1, -U 0 1; -U 1 0, U 0 0]
  have hUA : U * A = 1 := by
    ext i j
    have hd := hdet
    rw [Matrix.det_fin_two] at hd
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | exact hd | linear_combination hd | ring
  have hU : U.conjTranspose * U = 1 := hu.1
  have hA : U.conjTranspose = A := by
    calc
      _ = U.conjTranspose * (U * A) := by rw [hUA, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have ha := congrArg (fun M : Operator (Fin 2) => M 0 0) hA
  have hb := congrArg (fun M : Operator (Fin 2) => M 1 0) hA
  change star (U 0 0) = U 1 1 at ha
  change star (U 0 1) = - U 1 0 at hb
  have hc : U 1 0 = -star (U 0 1) := by rw [hb, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc, ← ha]

private theorem first_row_norm_sq (U : Operator (Fin 2)) (hu : IsUnitary U) :
    ‖U 0 0‖ ^ 2 + ‖U 0 1‖ ^ 2 = 1 := by
  have h := congrArg (fun M : Operator (Fin 2) => M 0 0) hu.2
  change (U * U.conjTranspose) 0 0 = (1 : Operator (Fin 2)) 0 0 at h
  have hconj (z : ℂ) : z * star z = (‖z‖ : ℂ) ^ 2 := Complex.mul_conj' z
  have hh : (‖U 0 0‖ : ℂ) ^ 2 + (‖U 0 1‖ : ℂ) ^ 2 = 1 := by
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq, hconj] using h
  have hr := congrArg Complex.re hh
  simpa only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] using hr

/-- Exact ZXZ factorization in SU(2), including cases where either of the
first-row entries vanishes. -/
theorem unitary_det_one_euler_zxz (U : Operator (Fin 2))
    (hu : IsUnitary U) (hdet : U.det = 1) :
    ∃ s t u : ℝ, U = rotation SinglePauli.Z.matrix s * rotation SinglePauli.X.matrix t *
      rotation SinglePauli.Z.matrix u := by
  let a := U 0 0
  let b := U 0 1
  let θ := Real.arccos ‖a‖
  let α := Complex.arg a
  let β := Complex.arg (-Complex.I * b)
  let s := (α + β) / 2
  let u := (α - β) / 2
  have hsum : s + u = α := by dsimp only [s, u]; ring
  have hsub : s - u = β := by dsimp only [s, u]; ring
  have hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := first_row_norm_sq U hu
  have hcos : Real.cos θ = ‖a‖ :=
    Real.cos_arccos (by linarith [norm_nonneg a])
      (by nlinarith [norm_nonneg a, sq_nonneg ‖b‖])
  have hsin : Real.sin θ = ‖b‖ := by
    change Real.sin (Real.arccos ‖a‖) = _
    rw [Real.sin_arccos, show 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg b)]
  have ha : (Real.cos θ : ℂ) * phase α = a := by
    rw [hcos]
    exact Complex.norm_mul_exp_arg_mul_I a
  have hb' : (Real.sin θ : ℂ) * phase β = -Complex.I * b := by
    rw [hsin]
    simpa [phase, β, norm_mul] using Complex.norm_mul_exp_arg_mul_I (-Complex.I * b)
  have hb : (Complex.I * (Real.sin θ : ℂ)) * phase β = b := by
    calc
      _ = Complex.I * ((Real.sin θ : ℂ) * phase β) := mul_assoc _ _ _
      _ = b := by rw [hb', ← mul_assoc]; simp [Complex.I_mul_I]
  have hac : (Real.cos θ : ℂ) * phase (-α) = star a := by
    have h := congrArg (star : ℂ → ℂ) ha
    simpa only [star_mul, star_ofReal, star_phase, mul_comm (phase (-α))] using h
  have hbc : (Complex.I * (Real.sin θ : ℂ)) * phase (-β) = -star b := by
    have h := congrArg (fun z : ℂ => -star z) hb
    simpa only [star_mul, star_phase, star_ofReal, star_I, mul_neg, neg_mul, neg_neg,
      mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨s, θ, u, ?_⟩
  rw [rotation_zxz_entries, hsum, hsub, ha, hb, hac, hbc]
  exact unitary_det_one_eq_entries U hu hdet

/-- Every qubit projective unitary has a word of three alternating
continuous-axis rotations. -/
theorem projective_euler_zxz (V : PU (Fin 2)) :
    ∃ s t u : ℝ, V = projectiveZ s * projectiveX t * projectiveZ u := by
  induction V using Quotient.inductionOn with
  | _ W =>
    let U : Operator (Fin 2) := W.val
    have hu : IsUnitary U := W.property
    have hdetUnit : star U.det * U.det = 1 := by
      have hU : U.conjTranspose * U = 1 := hu.1
      have h := congrArg Matrix.det hU
      simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] using h
    have hnorm : ‖U.det‖ = 1 := by
      have h := hdetUnit
      rw [mul_comm, show star U.det = starRingEnd ℂ U.det from rfl, Complex.mul_conj'] at h
      have hr := congrArg Complex.re h
      simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at hr
      nlinarith [norm_nonneg U.det]
    let t := -(Complex.arg U.det) / 2
    let z := phase t
    have hz : star z * z = 1 := phase_unit t
    have hdphase : phase (Complex.arg U.det) = U.det := by
      have h := Complex.norm_mul_exp_arg_mul_I U.det
      simpa [phase, hnorm] using h
    have hzd : (z • U).det = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin, pow_two]
      change phase t * phase t * U.det = 1
      rw [← phase_add, ← hdphase, ← phase_add]
      have ht : t + t + Complex.arg U.det = 0 := by dsimp only [t]; ring
      rw [ht]
      simp [phase]
    let W' : Matrix.unitaryGroup (Fin 2) ℂ := ⟨z • U, unitary_smul_of_phase z U hz hu⟩
    obtain ⟨s, r, u, hEuler⟩ :=
      unitary_det_one_euler_zxz (z • U) W'.property hzd
    have hEq : W' =
        unitaryRotation SinglePauli.Z.matrix zSelf zSquare s *
          unitaryRotation SinglePauli.X.matrix xSelf xSquare r *
          unitaryRotation SinglePauli.Z.matrix zSelf zSquare u := by
      apply Subtype.ext
      exact hEuler
    refine ⟨s, r, u, ?_⟩
    have hq : projectiveMk (Fin 2) W' = projectiveMk (Fin 2) W :=
      (projectiveMk_eq_iff (Fin 2) W' W).mpr ⟨z, hz, rfl⟩
    change projectiveMk (Fin 2) W = _
    rw [← hq, hEq, map_mul, map_mul]
    rfl

/-- The two continuous Pauli axes generate the entire qubit projective
unitary group by finite words. -/
theorem subgroup_eq_top_of_has_XZ (G : Subgroup (PU (Fin 2)))
    (hx : ∀ t, projectiveX t ∈ G) (hz : ∀ t, projectiveZ t ∈ G) : G = ⊤ := by
  apply top_unique
  intro V _
  obtain ⟨s, t, u, rfl⟩ := projective_euler_zxz V
  exact G.mul_mem (G.mul_mem (hz s) (hx t)) (hz u)

#print axioms unitary_det_one_eq_entries
#print axioms unitary_det_one_euler_zxz
#print axioms projective_euler_zxz
#print axioms subgroup_eq_top_of_has_XZ

end

end CriticalDepth.Manuscript20261114.OneQubitEuler
