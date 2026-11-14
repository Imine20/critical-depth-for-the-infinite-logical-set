import CriticalDepthMathlib

/-!
# Exact CZ, CNOT, and SWAP identities
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped BigOperators Kronecker

noncomputable section

def pairZLeft : Operator (Fin 2 × Fin 2) := SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin 2))
def pairZRight : Operator (Fin 2 × Fin 2) := (1 : Operator (Fin 2)) ⊗ₖ SinglePauli.Z.matrix

/-- Controlled Z with the first bit controlling the second. -/
def pairCZ : Operator (Fin 2 × Fin 2) :=
  diagonal (fun x => if x.1 = 1 ∧ x.2 = 1 then -1 else 1)

private def h : ℂ := (Real.sqrt 2 / 2 : ℝ)

def pairHadamard : Operator (Fin 2) :=
  h • !![1, 1; 1, -1]

private theorem h_sq : h ^ 2 = 1 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hh : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by nlinarith
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hh
  simpa [h] using hc

private theorem pairHadamard_sq : pairHadamard * pairHadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairHadamard, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, smul_eq_mul] <;>
    first | linear_combination 2 * h_sq | ring

private theorem pairHadamard_conjugates_Z :
    pairHadamard * SinglePauli.Z.matrix * pairHadamard = SinglePauli.X.matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairHadamard, Matrix.mul_apply, Fin.sum_univ_two, SinglePauli.matrix, smul_eq_mul] <;>
    first | linear_combination 2 * h_sq | ring

private theorem circle_exp_quarter :
    (Circle.exp (Real.pi / 4) : ℂ) = h + h * Complex.I := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  rfl

private theorem pairZLeft_diag :
    pairZLeft = diagonal (fun x : Fin 2 × Fin 2 => if x.1 = 0 then 1 else -1) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pairZLeft, Matrix.kronecker_apply, Matrix.one_apply, SinglePauli.matrix, Matrix.diagonal_apply]

private theorem pairZRight_diag :
    pairZRight = diagonal (fun x : Fin 2 × Fin 2 => if x.2 = 0 then 1 else -1) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pairZRight, Matrix.kronecker_apply, Matrix.one_apply, SinglePauli.matrix, Matrix.diagonal_apply]

private theorem rotation_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (t : ℝ) :
    rotation (diagonal f) t =
      diagonal (fun i => (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) * f i) := by
  ext i j
  by_cases he : i = j
  · subst j
    simp [rotation, affine, Matrix.smul_apply, smul_eq_mul]
  · simp [rotation, affine, Matrix.one_apply_ne he, Matrix.diagonal_apply_ne _ he,
      Matrix.smul_apply, smul_eq_mul]

/-- The two local Z rotations and one ZZ rotation give exactly controlled
Z when the scalar displayed in the manuscript is included. -/
theorem pairCZ_eq_Z_Z_ZZ :
    pairCZ = (Circle.exp (Real.pi / 4) : ℂ) •
      (rotation pairZLeft (-Real.pi / 4) * rotation pairZRight (-Real.pi / 4) *
        rotation (pairZLeft * pairZRight) (Real.pi / 4)) := by
  rw [pairCZ, pairZLeft_diag, pairZRight_diag, Matrix.diagonal_mul_diagonal]
  simp only [rotation_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  apply congrArg diagonal
  funext x
  obtain ⟨a,b⟩ := x
  have hI₂ : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  have hI₃ : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI₂, neg_one_mul]
  have hI₄ : Complex.I ^ 4 = 1 := by rw [pow_succ, hI₃, neg_mul, Complex.I_mul_I, neg_neg]
  rw [circle_exp_quarter]
  have hc : (Real.cos (-Real.pi / 4) : ℂ) = h := by
    rw [show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg, Real.cos_pi_div_four]
    rfl
  have hs : (Real.sin (-Real.pi / 4) : ℂ) = -h := by
    rw [show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.sin_neg, Real.sin_pi_div_four,
      Complex.ofReal_neg]
    rfl
  have hc' : (Real.cos (Real.pi / 4) : ℂ) = h := by rw [Real.cos_pi_div_four]; rfl
  have hs' : (Real.sin (Real.pi / 4) : ℂ) = h := by rw [Real.sin_pi_div_four]; rfl
  simp only [hc, hs, hc', hs']
  fin_cases a <;> fin_cases b <;>
    norm_num [Pi.smul_apply, smul_eq_mul] <;>
    ring_nf <;> simp only [hI₂, hI₃, hI₄] <;>
    first | linear_combination 4 * (h ^ 2 + 1 / 2) * h_sq |
      linear_combination -4 * (h ^ 2 + 1 / 2) * h_sq

/-- Basis-controlled X where the first bit is the control. -/
def pairCNOT : Operator (Fin 2 × Fin 2) :=
  fun x y => if x.1 = y.1 then
    (if y.1 = 0 then (1 : Operator (Fin 2)) else SinglePauli.X.matrix) x.2 y.2 else 0

def pairReverseCNOT : Operator (Fin 2 × Fin 2) :=
  fun x y => pairCNOT x.swap y.swap

def pairSwap : Operator (Fin 2 × Fin 2) :=
  fun x y => if x = y.swap then 1 else 0

/-- Hadamard on the target conjugates controlled Z to controlled X. -/
theorem pairCNOT_eq_targetHadamard_CZ :
    pairCNOT = ((1 : Operator (Fin 2)) ⊗ₖ pairHadamard) * pairCZ *
      ((1 : Operator (Fin 2)) ⊗ₖ pairHadamard) := by
  let M := (1 : Operator (Fin 2)) ⊗ₖ pairHadamard
  have hsum (x y : Fin 2 × Fin 2) :
      (M * pairCZ * M) x y =
        if x.1 = y.1 then
          (pairHadamard *
            (if y.1 = 0 then (1 : Operator (Fin 2)) else SinglePauli.Z.matrix) *
            pairHadamard) x.2 y.2
        else 0 := by
    obtain ⟨a,b⟩ := x
    obtain ⟨c,d⟩ := y
    rw [pairCZ, Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    rw [Fintype.sum_prod_type]
    fin_cases a <;> fin_cases c <;> simp [M, Matrix.kronecker_apply, Matrix.one_apply,
      Fin.sum_univ_two, Matrix.mul_apply, SinglePauli.matrix] <;> ring
  ext x y
  change _ = (M * pairCZ * M) x y
  rw [hsum]
  unfold pairCNOT
  split
  · split
    · rw [Matrix.mul_one, pairHadamard_sq]
    · rw [pairHadamard_conjugates_Z]
  · rfl

/-- Three CNOTs in alternating orientation swap the two sites. -/
theorem pairSwap_eq_CNOT_reverseCNOT_CNOT :
    pairSwap = pairCNOT * pairReverseCNOT * pairCNOT := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pairSwap, pairCNOT, pairReverseCNOT, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, SinglePauli.matrix, Prod.swap, Matrix.one_apply]

#print axioms pairCZ_eq_Z_Z_ZZ
#print axioms pairCNOT_eq_targetHadamard_CZ
#print axioms pairSwap_eq_CNOT_reverseCNOT_CNOT

end

end CriticalDepth.Manuscript20261114
