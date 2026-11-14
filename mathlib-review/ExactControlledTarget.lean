import ExactConditionalRotation
import CliffordTWords
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Exact two-level compilation in a computational one-bit block
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open CriticalDepth.Manuscript20261114.OneQubitEuler
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {k : ℕ}

/-- The target bit and all remaining site values index the computational register. -/
def splitTargetBit (j : Fin k) : Fin 2 × ({i : Fin k // i ≠ j} → Fin 2) ≃ QubitBasis k where
  toFun p i := if h : i = j then p.1 else p.2 ⟨i, h⟩
  invFun b := (b j, fun i => b i.val)
  left_inv p := by
    apply Prod.ext
    · simp
    · funext i
      exact dif_neg i.property
  right_inv b := by
    funext i
    by_cases h : i = j
    · subst i; simp
    · simp [h]

variable (j : Fin k)

private abbrev RemainingBits (j : Fin k) := {i : Fin k // i ≠ j} → Fin 2

def controlComplements (j : Fin k) : Finset (Fin k) := Finset.univ.erase j

def controlBits (j : Fin k) (y : QubitBasis k) : RemainingBits j :=
  fun i => y i.val

private theorem agrees_controls_iff (y x : QubitBasis k) :
    (∀ i ∈ controlComplements j, x i = y i) ↔ controlBits j x = controlBits j y := by
  constructor
  · intro h
    funext i
    exact h i.val (Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩)
  · intro h i hi
    exact congrFun h ⟨i, (Finset.mem_erase.mp hi).1⟩

/-- Prescribed matrix on the target block singled out by a complete
control pattern and identity on every other target block. -/
def controlledTarget (y : QubitBasis k) (A : Operator (Fin 2)) : Operator (QubitBasis k) :=
  reindex (splitTargetBit j) (splitTargetBit j)
    (blockDiagonal fun z : RemainingBits j => if z = controlBits j y then A else 1)

theorem controlledTarget_apply (y : QubitBasis k) (A : Operator (Fin 2))
    (x x' : QubitBasis k) :
    controlledTarget j y A x x' =
      if controlBits j x = controlBits j x' then
        (if controlBits j x = controlBits j y then A else 1) (x j) (x' j)
      else 0 := by
  unfold controlledTarget
  change (blockDiagonal fun z : RemainingBits j => if z = controlBits j y then A else 1)
    (x j, controlBits j x) (x' j, controlBits j x') = _
  rw [blockDiagonal_apply]

theorem controlledTarget_mul (y : QubitBasis k) (A B : Operator (Fin 2)) :
    controlledTarget j y A * controlledTarget j y B = controlledTarget j y (A * B) := by
  unfold controlledTarget
  change reindexAlgEquiv ℂ ℂ (splitTargetBit j) _ *
    reindexAlgEquiv ℂ ℂ (splitTargetBit j) _ = reindexAlgEquiv ℂ ℂ (splitTargetBit j) _
  rw [← map_mul, ← blockDiagonal_mul]
  congr 2
  funext z
  by_cases h : z = controlBits j y <;> simp [h]

theorem controlledTarget_scalar (y : QubitBasis k) (t : ℝ) :
    controlledTarget j y ((Circle.exp t : ℂ) • 1) =
      conditionalPhase (controlComplements j) y t := by
  classical
  ext x x'
  rw [controlledTarget_apply, conditionalPhase, diagonal_apply]
  have hc := (agrees_controls_iff j y x)
  simp only [hc]
  by_cases hControl : controlBits j x = controlBits j x'
  · have hEq : x = x' ↔ x j = x' j := by
      refine ⟨fun h => congrArg (fun x : QubitBasis k => x j) h, ?_⟩
      intro h
      exact (splitTargetBit j).symm.injective (Prod.ext h hControl)
    by_cases hy : controlBits j x' = controlBits j y <;>
      by_cases hxy : x j = x' j <;>
      simp [hControl, hEq, hy, hxy, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  · have hh : x ≠ x' := fun h => hControl (congrArg (controlBits j) h)
    simp [hControl, hh]

private theorem singleSitePauli_eq_targetBlocks (A : SinglePauli) :
    pauliMatrix 0 (singleSitePauli j A) =
      reindex (splitTargetBit j) (splitTargetBit j) (blockDiagonal fun _ : RemainingBits j => A.matrix) := by
  classical
  ext x y
  rw [pauliMatrix_zero_eq_tensorEntries]
  change (∏ i, (singleSitePauli j A i).matrix (x i) (y i)) =
    (blockDiagonal fun _ : RemainingBits j => A.matrix) (x j, controlBits j x) (y j, controlBits j y)
  rw [blockDiagonal_apply]
  by_cases h : controlBits j x = controlBits j y
  · rw [ite_eq_left h]
    rw [Finset.prod_eq_single j]
    · simp [singleSitePauli]
    · intro i _ hi
      have he : x i = y i := congrFun h ⟨i, hi⟩
      simp [singleSitePauli, hi, SinglePauli.matrix, Matrix.one_apply, he]
    · simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    simp [singleSitePauli, i.property, SinglePauli.matrix, Matrix.one_apply, controlBits] at hi ⊢
    exact hi

private theorem projectedTarget_eq_blocks (y : QubitBasis k) (A : SinglePauli) (t : ℝ) :
    ((Complex.I * (t : ℂ)) • controlProjector (controlComplements j) y) *
      pauliMatrix 0 (singleSitePauli j A) =
        reindex (splitTargetBit j) (splitTargetBit j)
          (blockDiagonal fun z : RemainingBits j =>
            if z = controlBits j y then (Complex.I * (t : ℂ)) • A.matrix else 0) := by
  rw [controlProjector, ← Matrix.diagonal_smul, singleSitePauli_eq_targetBlocks]
  ext x x'
  rw [Matrix.diagonal_mul]
  change (Complex.I * (t : ℂ) * controlIndicator (controlComplements j) y x) *
    (blockDiagonal fun _ : RemainingBits j => A.matrix) (x j, controlBits j x) (x' j, controlBits j x') =
      (blockDiagonal fun z : RemainingBits j =>
        if z = controlBits j y then (Complex.I * (t : ℂ)) • A.matrix else 0)
        (x j, controlBits j x) (x' j, controlBits j x')
  simp only [blockDiagonal_apply, controlIndicator, agrees_controls_iff]
  by_cases h : controlBits j x = controlBits j x'
  · by_cases hy : controlBits j x' = controlBits j y <;>
      simp [h, hy, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  · simp [h]

/-- The exactly synthesized controlled exponential acts by the usual
rotation on its selected block and identity elsewhere. -/
theorem controlledTarget_rotation (y : QubitBasis k) (A : SinglePauli) (t : ℝ) :
    controlledTarget j y (rotation A.matrix t) =
      conditionalRotation (controlComplements j) y j A t := by
  classical
  unfold conditionalRotation
  rw [projectedTarget_eq_blocks]
  let φ := (reindexRingEquiv ℂ (splitTargetBit j)).toRingHom
  have hφ : Continuous φ := by
    apply continuous_matrix
    intro x x'
    change Continuous fun M : Operator (Fin 2 × RemainingBits j) =>
      M ((splitTargetBit j).symm x) ((splitTargetBit j).symm x')
    exact continuous_id.matrix_elem _ _
  let f (z : RemainingBits j) := if z = controlBits j y then (Complex.I * (t : ℂ)) • A.matrix else 0
  change controlledTarget j y (rotation A.matrix t) = NormedSpace.exp (φ (blockDiagonal f))
  letI : NormedAlgebra ℚ (Operator (Fin 2 × RemainingBits j)) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [← NormedSpace.map_exp φ hφ, Matrix.exp_blockDiagonal]
  unfold controlledTarget
  change φ (blockDiagonal _) = φ (blockDiagonal _)
  congr 2
  funext z
  letI : NormedAlgebra ℚ (Operator (Fin 2)) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hExp : NormedSpace.exp f z = NormedSpace.exp (f z) := Pi.coe_exp f z
  rw [hExp]
  by_cases hz : z = controlBits j y
  · rw [if_pos hz, show f z = (Complex.I * (t : ℂ)) • A.matrix from if_pos hz]
    exact (exp_involution_eq_rotation (singlePauli_sq A) t).symm
  · simp only [if_neg hz, f, NormedSpace.exp_zero]

/-- Controlled X is the phase-retaining product from the manuscript. -/
theorem controlledTarget_X_eq_conditional_factors (y : QubitBasis k) :
    controlledTarget j y SinglePauli.X.matrix =
      conditionalPhase (controlComplements j) y (Real.pi / 2) *
        conditionalRotation (controlComplements j) y j .X (-Real.pi / 2) := by
  rw [← controlledTarget_scalar, ← controlledTarget_rotation, controlledTarget_mul]
  congr 1
  have hI : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
    rw [Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [hI, show -Real.pi / 2 = -(Real.pi / 2) by ring, rotation, affine,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [Matrix.smul_mul, smul_smul, Complex.I_mul_I]

/-- The complete control pattern singles out the two adjacent words,
so controlled X acts by interchanging those two words alone. -/
theorem controlledTarget_X_entry (p x y : QubitBasis k) :
    controlledTarget j p SinglePauli.X.matrix x y =
      if x = (if controlBits j y = controlBits j p then
        Function.update y j (if y j = 0 then 1 else 0) else y) then 1 else 0 := by
  classical
  rw [controlledTarget_apply]
  let z := Function.update y j (if y j = 0 then 1 else 0)
  have hcz : controlBits j z = controlBits j y := by
    funext i
    exact Function.update_of_ne i.property _ _
  by_cases hxy : controlBits j x = controlBits j y
  · rw [ite_eq_left hxy]
    by_cases hp : controlBits j y = controlBits j p
    · rw [ite_eq_left hp, ite_eq_left (hxy.trans hp)]
      have he : x = z ↔ x j = z j := by
        refine ⟨fun h => congrArg (fun w : QubitBasis k => w j) h, ?_⟩
        intro h
        exact (splitTargetBit j).symm.injective (Prod.ext h (hxy.trans hcz.symm))
      change SinglePauli.X.matrix (x j) (y j) = if x = z then 1 else 0
      simp only [he, show z j = (if y j = 0 then 1 else 0) from Function.update_self _ _ _]
      have hBit (b : Fin 2) : b = 0 ∨ b = 1 := by fin_cases b <;> simp
      rcases hBit (x j) with hx | hx <;> rcases hBit (y j) with hy | hy <;>
        simp [SinglePauli.matrix, hx, hy]
    · rw [ite_eq_right hp, ite_eq_right (fun h => hp (hxy.symm.trans h))]
      have he : x = y ↔ x j = y j := by
        refine ⟨fun h => congrArg (fun w : QubitBasis k => w j) h, ?_⟩
        intro h
        exact (splitTargetBit j).symm.injective (Prod.ext h hxy)
      simp only [Matrix.one_apply, he]
  · rw [ite_eq_right hxy]
    split
    · exact (ite_eq_right (fun h => hxy ((congrArg (controlBits j) h).trans hcz))).symm
    · exact (ite_eq_right (fun h => hxy (congrArg (controlBits j) h))).symm

#print axioms controlledTarget_mul
#print axioms controlledTarget_rotation
#print axioms controlledTarget_X_eq_conditional_factors

end

end CriticalDepth.Manuscript20261114
