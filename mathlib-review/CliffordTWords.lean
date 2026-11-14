import CliffordTMixedAxis

/-!
# Clifford–T finite-word identities on the logical qubit
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114.OneQubitEuler Matrix
open scoped BigOperators

noncomputable section

private def hScale : ℝ := Real.sqrt 2 / 2

/-- The usual real Hadamard matrix. -/
def hadamardMatrix : QubitOperator :=
  (hScale : ℂ) • !![1, 1; 1, -1]

private theorem hScale_sq : (hScale : ℂ) * (hScale : ℂ) = 1 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hr : hScale * hScale = 1 / 2 := by unfold hScale; nlinarith
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

theorem hadamardMatrix_selfAdjoint : star hadamardMatrix = hadamardMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.star_def]

theorem hadamardMatrix_sq : hadamardMatrix * hadamardMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, hScale_sq] <;> norm_num

def hadamardUnitary : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨hadamardMatrix, by
    constructor <;> rw [hadamardMatrix_selfAdjoint, hadamardMatrix_sq]⟩

def projectiveHadamard : PU (Fin 2) := projectiveMk (Fin 2) hadamardUnitary

/-- T is projectively exactly the real −π/8 Z rotation. -/
def projectiveT : PU (Fin 2) := projectiveZ (-eighthTurn)

theorem hadamard_conjugates_Z :
    hadamardMatrix * SinglePauli.Z.matrix * hadamardMatrix = SinglePauli.X.matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_two, SinglePauli.matrix,
      Matrix.smul_apply, smul_eq_mul, hScale_sq] <;> ring

private theorem hadamardUnitary_inv : hadamardUnitary⁻¹ = hadamardUnitary := by
  apply Subtype.ext
  exact hadamardMatrix_selfAdjoint

theorem projectiveHadamard_conjugates_rotationZ (t : ℝ) :
    projectiveHadamard * projectiveZ t * projectiveHadamard⁻¹ = projectiveX t := by
  unfold projectiveHadamard projectiveZ projectiveX projectiveRotation
  rw [← map_inv, ← map_mul, ← map_mul, hadamardUnitary_inv]
  apply congrArg (projectiveMk (Fin 2))
  apply Subtype.ext
  change hadamardMatrix * rotation SinglePauli.Z.matrix t * hadamardMatrix =
    rotation SinglePauli.X.matrix t
  simp only [rotation, affine, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hadamardMatrix_sq]
  rw [hadamard_conjugates_Z]

theorem projectiveZ_add (s t : ℝ) :
    projectiveZ (s + t) = projectiveZ s * projectiveZ t := by
  unfold projectiveZ projectiveRotation
  rw [← map_mul]
  apply congrArg (projectiveMk (Fin 2))
  apply Subtype.ext
  exact rotation_add (singlePauli_sq .Z) s t

theorem projectiveZ_neg (s : ℝ) : projectiveZ (-s) = (projectiveZ s)⁻¹ := by
  unfold projectiveZ projectiveRotation
  rw [← map_inv]
  apply congrArg (projectiveMk (Fin 2))
  apply Subtype.ext
  change rotation SinglePauli.Z.matrix (-s) = star (rotation SinglePauli.Z.matrix s)
  exact (star_rotation (singlePauli_selfAdjoint .Z) s).symm

/-- The projective classes represented by manuscript's depth-one D and B. -/
def projectiveD : PU (Fin 2) := projectiveZ eighthTurn

def projectiveB : PU (Fin 2) := projectiveX (Real.pi / 4)

theorem projectiveD_inv_eq_T : projectiveD⁻¹ = projectiveT := by
  unfold projectiveD projectiveT
  exact (projectiveZ_neg eighthTurn).symm

/-- The three factors in D² B D² use five depth-one generators. -/
theorem projectiveD_sq_mul_B_mul_D_sq : projectiveD ^ 2 * projectiveB * projectiveD ^ 2 =
    projectiveHadamard := by
  have hD : projectiveD ^ 2 = projectiveZ (Real.pi / 4) := by
    unfold projectiveD
    rw [pow_two, ← projectiveZ_add]
    congr 1
    unfold eighthTurn
    ring
  rw [hD]
  unfold projectiveHadamard projectiveZ projectiveB projectiveX projectiveRotation
  rw [← map_mul, ← map_mul]
  apply (projectiveMk_eq_iff (Fin 2) _ _).mpr
  refine ⟨Complex.I, ?_, ?_⟩
  · simp [Complex.star_def, Complex.I_mul_I]
  change rotation SinglePauli.Z.matrix (Real.pi / 4) *
    rotation SinglePauli.X.matrix (Real.pi / 4) *
    rotation SinglePauli.Z.matrix (Real.pi / 4) = Complex.I • hadamardMatrix
  have hcosPos : Real.cos (Real.pi / 4) = hScale := Real.cos_pi_div_four
  have hsinPos : Real.sin (Real.pi / 4) = hScale := Real.sin_pi_div_four
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, affine, SinglePauli.matrix, Matrix.mul_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two,
      hcosPos, hsinPos, hadamardMatrix] <;>
    ring_nf <;> try simp only [Complex.I_sq,
      show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq, neg_one_mul]] <;>
    first | linear_combination (2 * Complex.I * (hScale : ℂ)) * hScale_sq |
      linear_combination (-2 * Complex.I * (hScale : ℂ)) * hScale_sq | ring

#print axioms projectiveHadamard_conjugates_rotationZ
#print axioms projectiveD_inv_eq_T
#print axioms projectiveD_sq_mul_B_mul_D_sq

end

end CriticalDepth.Manuscript20261114.CliffordT
