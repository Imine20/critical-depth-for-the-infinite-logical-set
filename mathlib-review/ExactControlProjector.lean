import CriticalDepthMathlib
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Control projectors as exact sums of commuting Z strings
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix
open scoped BigOperators

noncomputable section

variable {k : ℕ}

/-- The sign of a Z factor on a computational basis bit. -/
def logicalBitSign (b : Fin 2) : ℂ := if b = 0 then 1 else -1

def controlIndicator (B : Finset (Fin k)) (y x : QubitBasis k) : ℂ :=
  if ∀ i ∈ B, x i = y i then 1 else 0

/-- The exact projector for the pattern y on the selected control sites. -/
def controlProjector (B : Finset (Fin k)) (y : QubitBasis k) : Operator (QubitBasis k) :=
  Matrix.diagonal (controlIndicator B y)

def zSubset (S : Finset (Fin k)) : Fin k → SinglePauli :=
  fun i => if i ∈ S then .Z else .I

/-- A tensor Z mask is diagonal, with eigenvalue the product of its bit signs. -/
theorem pauliMatrix_zSubset (S : Finset (Fin k)) :
    pauliMatrix 0 (zSubset S) =
      Matrix.diagonal (fun x : QubitBasis k => ∏ i ∈ S, logicalBitSign (x i)) := by
  classical
  have hz (a b : Fin 2) :
      SinglePauli.Z.matrix a b = Matrix.diagonal logicalBitSign a b := by
    fin_cases a <;> fin_cases b <;> simp [SinglePauli.matrix, logicalBitSign, Matrix.diagonal_apply]
  ext x x'
  rw [pauliMatrix_zero_eq_tensorEntries]
  change (∏ i, (zSubset S i).matrix (x i) (x' i)) = _
  by_cases hx : x = x'
  · subst x'
    rw [Matrix.diagonal_apply_eq]
    calc
      _ = ∏ i : Fin k, if i ∈ S then logicalBitSign (x i) else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp only [zSubset, if_pos hi, hz, Matrix.diagonal_apply_eq]
        · simp [zSubset, hi, SinglePauli.matrix]
      _ = _ := by
        have hfilter : (Finset.univ : Finset (Fin k)).filter (· ∈ S) = S := by
          ext i
          simp
        simpa only [hfilter] using
          (Finset.prod_filter (s := (Finset.univ : Finset (Fin k)))
            (· ∈ S) (fun i => logicalBitSign (x i))).symm
  · rw [Matrix.diagonal_apply_ne _ hx]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := Function.ne_iff.mp hx
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases h : i ∈ S
    · simpa [zSubset, h, hz] using Matrix.diagonal_apply_ne logicalBitSign hi
    · simp [zSubset, h, SinglePauli.matrix, Matrix.one_apply, hi]

private theorem logicalBitSign_mul (x y : Fin 2) :
    logicalBitSign y * logicalBitSign x = if x = y then 1 else -1 := by
  fin_cases x <;> fin_cases y <;> norm_num [logicalBitSign]

private theorem indicator_eq_zSum (B : Finset (Fin k)) (y x : QubitBasis k) :
    controlIndicator B y x =
      (2 : ℂ)⁻¹ ^ B.card *
        ∑ T ∈ B.powerset, (∏ i ∈ T, logicalBitSign (y i)) * ∏ i ∈ T, logicalBitSign (x i) := by
  classical
  let f : Fin k → ℂ := fun i => logicalBitSign (y i) * logicalBitSign (x i)
  have hprod : (∏ i ∈ B, (1 + f i)) =
      ∑ T ∈ B.powerset, (∏ i ∈ T, logicalBitSign (y i)) * ∏ i ∈ T, logicalBitSign (x i) := by
    rw [Finset.prod_one_add]
    exact Finset.sum_congr rfl (fun T _ => Finset.prod_mul_distrib)
  rw [← hprod]
  unfold controlIndicator
  by_cases h : ∀ i ∈ B, x i = y i
  · rw [ite_eq_left h]
    have hp : ∏ i ∈ B, (1 + f i) = 2 ^ B.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl (fun i hi => ?_)
      norm_num [f, logicalBitSign_mul, h i hi]
    rw [hp, ← mul_pow]
    norm_num
  · rw [ite_eq_right h]
    push_neg at h
    obtain ⟨i, hi, hxy⟩ := h
    have hp : ∏ j ∈ B, (1 + f j) = 0 := by
      apply Finset.prod_eq_zero hi
      simp [f, logicalBitSign_mul, hxy]
    rw [hp, mul_zero]

/-- The product expansion for the control projector. The register
coordinates outside the control set do not appear in any summand. -/
theorem controlProjector_eq_pauliSum (B : Finset (Fin k)) (y : QubitBasis k) :
    controlProjector B y =
      (2 : ℂ)⁻¹ ^ B.card •
        ∑ T ∈ B.powerset, (∏ i ∈ T, logicalBitSign (y i)) • pauliMatrix 0 (zSubset T) := by
  classical
  ext x x'
  simp only [controlProjector, pauliMatrix_zSubset, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  by_cases h : x = x'
  · subst x'
    simp only [Matrix.diagonal_apply_eq]
    exact indicator_eq_zSum B y x
  · simp [Matrix.diagonal_apply_ne _ h]

theorem commute_pauliMatrix_zSubset (A B : Finset (Fin k)) :
    Commute (pauliMatrix 0 (zSubset A)) (pauliMatrix 0 (zSubset B)) := by
  rw [pauliMatrix_zSubset, pauliMatrix_zSubset]
  show _ * _ = _ * _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

#print axioms controlProjector_eq_pauliSum
#print axioms commute_pauliMatrix_zSubset

end

end CriticalDepth.Manuscript20261114
