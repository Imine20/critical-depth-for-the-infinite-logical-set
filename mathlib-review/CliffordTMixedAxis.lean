import CliffordTIrrationalAngle
import OneQubitEuler

/-!
# Axis and angle of the product of the π/8 Z and X rotations
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114.OneQubitEuler Matrix
open scoped BigOperators

noncomputable section

abbrev QubitOperator := Operator (Fin 2)

def eighthTurn : ℝ := Real.pi / 8

def eighthCos : ℝ := Real.cos eighthTurn

def eighthSin : ℝ := Real.sin eighthTurn

def mixedQubitAngle : ℝ := Real.arccos (eighthCos ^ 2)

def mixedAxisX : ℝ := eighthCos * eighthSin / Real.sin mixedQubitAngle

def mixedAxisY : ℝ := -(eighthSin ^ 2) / Real.sin mixedQubitAngle

def mixedAxisZ : ℝ := eighthCos * eighthSin / Real.sin mixedQubitAngle

/-- A real Pauli combination, with coordinates in the order X, Y, Z. -/
def pauliCombination (a b c : ℝ) : QubitOperator :=
  (a : ℂ) • SinglePauli.X.matrix + (b : ℂ) • SinglePauli.Y.matrix +
    (c : ℂ) • SinglePauli.Z.matrix

def mixedAxis : QubitOperator := pauliCombination mixedAxisX mixedAxisY mixedAxisZ

private theorem eighthSin_pos : 0 < eighthSin := by
  unfold eighthSin eighthTurn
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

private theorem eighthCos_pos : 0 < eighthCos := by
  unfold eighthCos eighthTurn
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

private theorem eighthCos_sq_add_eighthSin_sq : eighthCos ^ 2 + eighthSin ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq eighthTurn

private theorem mixedQubitAngle_cos : Real.cos mixedQubitAngle = eighthCos ^ 2 := by
  apply Real.cos_arccos
  · nlinarith [sq_nonneg eighthCos]
  · nlinarith [eighthCos_sq_add_eighthSin_sq, sq_nonneg eighthSin]

theorem mixedQubitAngle_sin_pos : 0 < Real.sin mixedQubitAngle := by
  unfold mixedQubitAngle
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.2
  have h : eighthCos ^ 2 < 1 := by
    nlinarith [eighthCos_sq_add_eighthSin_sq, eighthSin_pos, sq_pos_of_pos eighthSin_pos]
  nlinarith [sq_nonneg eighthCos, mul_pos (by linarith : 0 < 1 - eighthCos ^ 2)
    (by positivity : 0 < 1 + eighthCos ^ 2)]

theorem mixedAxisX_pos : 0 < mixedAxisX :=
  div_pos (mul_pos eighthCos_pos eighthSin_pos) mixedQubitAngle_sin_pos

theorem mixedAxisZ_pos : 0 < mixedAxisZ :=
  div_pos (mul_pos eighthCos_pos eighthSin_pos) mixedQubitAngle_sin_pos

private theorem mixedAxis_unit_sphere :
    mixedAxisX ^ 2 + mixedAxisY ^ 2 + mixedAxisZ ^ 2 = 1 := by
  have hangle := Real.cos_sq_add_sin_sq mixedQubitAngle
  rw [mixedQubitAngle_cos] at hangle
  unfold mixedAxisX mixedAxisY mixedAxisZ
  field_simp [ne_of_gt mixedQubitAngle_sin_pos]
  nlinarith [hangle, eighthCos_sq_add_eighthSin_sq,
    congrArg (fun x : ℝ => x ^ 2) eighthCos_sq_add_eighthSin_sq]

theorem pauliCombination_selfAdjoint (a b c : ℝ) :
    star (pauliCombination a b c) = pauliCombination a b c := by
  unfold pauliCombination
  change (_ : QubitOperator).conjTranspose = _
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def,
    singlePauli_selfAdjoint]

theorem pauliCombination_sq (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    pauliCombination a b c * pauliCombination a b c = 1 := by
  have hc : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCombination, SinglePauli.matrix, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] <;>
    ring_nf <;> simp only [Complex.I_sq] <;>
    linear_combination hc

theorem mixedAxis_selfAdjoint : star mixedAxis = mixedAxis :=
  pauliCombination_selfAdjoint _ _ _

theorem mixedAxis_sq : mixedAxis * mixedAxis = 1 :=
  pauliCombination_sq _ _ _ mixedAxis_unit_sphere

theorem mixedQubitAngle_irrational : Irrational (mixedQubitAngle / Real.pi) := by
  apply irrational_angle_of_trace
  rw [mixedQubitAngle_cos]
  have h := Real.cos_two_mul eighthTurn
  have hs : 2 * eighthTurn = Real.pi / 4 := by unfold eighthTurn; ring
  rw [hs, Real.cos_pi_div_four] at h
  unfold eighthCos
  linarith

/-- Equal-angle Z and X rotations give the irrational-angle Pauli axis. -/
theorem rotationZ_mul_rotationX_eighthTurn :
    rotation SinglePauli.Z.matrix eighthTurn * rotation SinglePauli.X.matrix eighthTurn =
      rotation mixedAxis mixedQubitAngle := by
  let s := Real.sin mixedQubitAngle
  have hs : s ≠ 0 := ne_of_gt mixedQubitAngle_sin_pos
  have hX : s * mixedAxisX = eighthCos * eighthSin := by
    unfold mixedAxisX
    change s * (eighthCos * eighthSin / s) = _
    exact mul_div_cancel₀ _ hs
  have hY : s * mixedAxisY = -(eighthSin ^ 2) := by
    unfold mixedAxisY
    change s * (-(eighthSin ^ 2) / s) = _
    exact mul_div_cancel₀ _ hs
  have hZ : s * mixedAxisZ = eighthCos * eighthSin := hX
  have hx : (s : ℂ) * (mixedAxisX : ℂ) = (eighthCos : ℂ) * (eighthSin : ℂ) := by exact_mod_cast hX
  have hy : (s : ℂ) * (mixedAxisY : ℂ) = -(eighthSin : ℂ) ^ 2 := by exact_mod_cast hY
  have hz : (s : ℂ) * (mixedAxisZ : ℂ) = (eighthCos : ℂ) * (eighthSin : ℂ) := by exact_mod_cast hZ
  have hsAngle : Real.sin mixedQubitAngle = s := rfl
  have hcEighth : Real.cos eighthTurn = eighthCos := rfl
  have hsEighth : Real.sin eighthTurn = eighthSin := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, affine, mixedAxis, pauliCombination, mixedQubitAngle_cos,
      hsAngle, hcEighth, hsEighth, Matrix.mul_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two, SinglePauli.matrix]
  · linear_combination -Complex.I * hz
  · linear_combination -Complex.I * hx + Complex.I ^ 2 * hy
  · linear_combination -Complex.I * hx - Complex.I ^ 2 * hy
  · linear_combination Complex.I * hz

theorem projectiveZ_mul_projectiveX_eighthTurn :
    projectiveZ eighthTurn * projectiveX eighthTurn =
      projectiveRotation mixedAxis mixedAxis_selfAdjoint mixedAxis_sq mixedQubitAngle := by
  unfold projectiveZ projectiveX projectiveRotation
  rw [← map_mul]
  apply congrArg (projectiveMk (Fin 2))
  apply Subtype.ext
  exact rotationZ_mul_rotationX_eighthTurn

#print axioms mixedQubitAngle_irrational
#print axioms rotationZ_mul_rotationX_eighthTurn
#print axioms projectiveZ_mul_projectiveX_eighthTurn

end

end CriticalDepth.Manuscript20261114.CliffordT
