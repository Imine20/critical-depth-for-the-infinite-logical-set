import ExactControlProjector
import TensorPauliTangents
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Finite Pauli words for computational-basis conditional phases
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped BigOperators

noncomputable section

variable {k : ℕ}

/-- Relative phase on the selected computational control pattern. -/
def conditionalPhase (B : Finset (Fin k)) (y : QubitBasis k) (t : ℝ) :
    Operator (QubitBasis k) :=
  Matrix.diagonal fun x => if ∀ i ∈ B, x i = y i then (Circle.exp t : ℂ) else 1

private theorem bitSignProduct_eq (T : Finset (Fin k)) (y : QubitBasis k) :
    (∏ i ∈ T, logicalBitSign (y i)) =
      (((∏ i ∈ T, if y i = 0 then (1 : ℝ) else -1) : ℝ) : ℂ) := by
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : y i = 0 <;> simp [logicalBitSign, hi]

/-- Angle of the tensor-Z term in the commuting projector expansion. -/
def conditionalPauliAngle (B T : Finset (Fin k)) (y : QubitBasis k) (t : ℝ) : ℝ :=
  t * (2 : ℝ)⁻¹ ^ B.card * ∏ i ∈ T, if y i = 0 then 1 else -1

private theorem imaginary_controlProjector_eq_sum (B : Finset (Fin k)) (y : QubitBasis k) (t : ℝ) :
    (Complex.I * (t : ℂ)) • controlProjector B y =
      ∑ T ∈ B.powerset, (Complex.I * (conditionalPauliAngle B T y t : ℂ)) •
        pauliMatrix 0 (zSubset T) := by
  rw [controlProjector_eq_pauliSum, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [smul_smul, bitSignProduct_eq]
  congr 1
  unfold conditionalPauliAngle
  push_cast
  ring

private theorem exp_imaginary_controlProjector_eq_phase
    (B : Finset (Fin k)) (y : QubitBasis k) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • controlProjector B y) =
      conditionalPhase B y t := by
  let d : QubitBasis k → ℂ := fun x => (Complex.I * (t : ℂ)) * controlIndicator B y x
  have hs : (Complex.I * (t : ℂ)) • controlProjector B y = Matrix.diagonal d := by
    rw [controlProjector, ← Matrix.diagonal_smul]
    rfl
  rw [hs, Matrix.exp_diagonal]
  unfold conditionalPhase
  apply congrArg Matrix.diagonal
  funext x
  rw [Pi.coe_exp]
  by_cases h : ∀ i ∈ B, x i = y i
  · have hd : d x = Complex.I * (t : ℂ) := by
      change Complex.I * (t : ℂ) * controlIndicator B y x = _
      rw [controlIndicator, if_pos h, mul_one]
    rw [hd, if_pos h, Circle.coe_exp, ← Complex.exp_eq_exp_ℂ, mul_comm]
  · have hd : d x = 0 := by
      change Complex.I * (t : ℂ) * controlIndicator B y x = _
      rw [controlIndicator, if_neg h, mul_zero]
    rw [hd, if_neg h, NormedSpace.exp_zero]

private theorem tensorUnitary_list_prod_val
    (L : List (Matrix.unitaryGroup (QubitBasis k) ℂ)) :
    L.prod.val = (L.map fun U => U.val).prod := by
  induction L with
  | nil => rfl
  | cons U L ih =>
    change U.val * L.prod.val = U.val * (L.map fun U => U.val).prod
    rw [ih]

/-- The Givens compiler's relative phase is a finite product of rotations
about the individual diagonal words from the control expansion. -/
theorem conditionalPhase_eq_finite_tensorPauliWord
    (B : Finset (Fin k)) (y : QubitBasis k) (t : ℝ) :
    ∃ L : List (Matrix.unitaryGroup (QubitBasis k) ℂ),
      (∀ U ∈ L, ∃ (T : Finset (Fin k)), T ⊆ B ∧
        U = tensorPauliRotation (zSubset T) (conditionalPauliAngle B T y t)) ∧
      L.prod.val = conditionalPhase B y t := by
  classical
  let A := fun T : Finset (Fin k) =>
    (Complex.I * (conditionalPauliAngle B T y t : ℂ)) • pauliMatrix 0 (zSubset T)
  have hc (P Q : Finset (Fin k)) : Commute (A P) (A Q) :=
    (commute_pauliMatrix_zSubset P Q).smul_left _ |>.smul_right _
  have hWord (L : List (Finset (Fin k))) : NormedSpace.exp (L.map A).sum =
      (L.map fun T => (tensorPauliRotation (zSubset T) (conditionalPauliAngle B T y t)).val).prod := by
    induction L with
    | nil => simp
    | cons P L ih =>
      have hcomm : Commute (A P) (L.map A).sum := by
        exact Commute.list_sum_right _ _ (fun Q hQ => by
          obtain ⟨T, _, rfl⟩ := List.mem_map.mp hQ
          exact hc P T)
      rw [List.map_cons, List.sum_cons, Matrix.exp_add_of_commute _ _ hcomm, ih, List.map_cons,
        List.prod_cons]
      congr 1
      change NormedSpace.exp (A P) = rotation (pauliMatrix 0 (zSubset P)) _
      exact (rotation_eq_exp_involution (unphased_pauliMatrix_sq _) _).symm
  refine ⟨B.powerset.toList.map
    (fun T => tensorPauliRotation (zSubset T) (conditionalPauliAngle B T y t)), ?_, ?_⟩
  · intro U h
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp h
    exact ⟨T, Finset.mem_powerset.mp (Finset.mem_toList.mp hT), rfl⟩
  · rw [← exp_imaginary_controlProjector_eq_phase, imaginary_controlProjector_eq_sum]
    rw [tensorUnitary_list_prod_val, List.map_map]
    have hsum := Finset.sum_map_toList B.powerset A
    rw [← hsum, hWord]
    rfl

#print axioms conditionalPhase_eq_finite_tensorPauliWord

end

end CriticalDepth.Manuscript20261114
