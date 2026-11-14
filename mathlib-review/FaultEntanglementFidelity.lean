import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Entanglement infidelity for a finite Kraus family

For the maximally mixed logical input, the entanglement fidelity is the
normalized sum of squared Kraus traces. Orthogonal projection of each
Kraus matrix onto the scalar identity gives an exact expression for its
infidelity and characterizes the zero-infidelity cases.
-/

namespace CriticalDepth.FaultEntanglementFidelity

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

private def logicalDim (ι : Type*) [Fintype ι] : ℝ := Fintype.card ι

/-- Entanglement fidelity with the maximally mixed logical input. -/
def fidelity (K : κ → Matrix ι ι ℂ) : ℝ :=
  (∑ j, Complex.normSq (K j).trace) / (logicalDim ι)^2

def loss (K : κ → Matrix ι ι ℂ) : ℝ := 1 - fidelity K

def scalarResidual (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A - (A.trace / (Fintype.card ι : ℂ)) • (1 : Matrix ι ι ℂ)

private theorem trace_star_self_nonneg (A : Matrix ι ι ℂ) :
    0 ≤ (A.conjTranspose * A).trace.re := by
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1

private theorem trace_star_self_re_eq_zero (A : Matrix ι ι ℂ) :
    (A.conjTranspose * A).trace.re = 0 ↔ A = 0 := by
  constructor
  · intro hr
    have hpos := Matrix.posSemidef_conjTranspose_mul_self A
    have him := (Complex.nonneg_iff.mp hpos.trace_nonneg).2
    have hz : (A.conjTranspose * A).trace = 0 := by
      apply Complex.ext
      · simpa using hr
      · simpa using him.symm
    exact Matrix.conjTranspose_mul_self_eq_zero.mp (hpos.trace_eq_zero_iff.mp hz)
  · rintro rfl
    simp

private theorem residual_trace_formula [Nonempty ι] (A : Matrix ι ι ℂ) :
    ((scalarResidual A).conjTranspose * scalarResidual A).trace.re =
      (A.conjTranspose * A).trace.re - Complex.normSq A.trace / logicalDim ι := by
  let D := (Fintype.card ι : ℂ)
  let a := A.trace / D
  have hD : D ≠ 0 := by
    change (Fintype.card ι : ℂ) ≠ 0
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι).ne'
  have hdstar : star D = D := by simp [D]
  have ha : star a = star A.trace / D := by
    simp [a, star_div₀, hdstar]
  have hComplex : ((scalarResidual A).conjTranspose * scalarResidual A).trace =
      (A.conjTranspose * A).trace - (Complex.normSq A.trace : ℂ) / D := by
    change ((A - a • (1 : Matrix ι ι ℂ)).conjTranspose *
      (A - a • (1 : Matrix ι ι ℂ))).trace = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_conjTranspose, Matrix.trace_one, smul_eq_mul]
    change _ = (A.conjTranspose * A).trace - (Complex.normSq A.trace : ℂ) / D
    rw [ha, Complex.normSq_eq_conj_mul_self]
    change _ = (A.conjTranspose * A).trace - (star A.trace * A.trace) / D
    dsimp only [a]
    field_simp [hD]
    <;> ring
  have hre := congrArg Complex.re hComplex
  change ((scalarResidual A).conjTranspose * scalarResidual A).trace.re =
    (A.conjTranspose * A).trace.re - Complex.normSq A.trace / (Fintype.card ι : ℝ)
  simpa only [Complex.sub_re, D, logicalDim, ← Complex.ofReal_natCast,
    Complex.div_ofReal_re, Complex.ofReal_re] using hre

/-- For trace-preserving Kraus data, the lost fidelity is the sum of the
squared Hilbert–Schmidt norms of the deviations from scalar identity. -/
theorem loss_eq_residual_trace [Nonempty ι] (K : κ → Matrix ι ι ℂ)
    (hTP : (∑ j, (K j).conjTranspose * K j) = 1) :
    loss K = (∑ j, ((scalarResidual (K j)).conjTranspose * scalarResidual (K j)).trace.re)
      / logicalDim ι := by
  have hD : 0 < logicalDim ι := by
    change 0 < (Fintype.card ι : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have htrace : (∑ j, ((K j).conjTranspose * K j).trace.re) = logicalDim ι := by
    have h := congrArg (fun A : Matrix ι ι ℂ => A.trace.re) hTP
    simpa [logicalDim, Matrix.trace_sum, Complex.re_sum] using h
  simp only [residual_trace_formula, Finset.sum_sub_distrib, ← Finset.sum_div, htrace,
    loss, fidelity]
  field_simp [hD.ne']
  <;> ring

theorem loss_nonneg [Nonempty ι] (K : κ → Matrix ι ι ℂ)
    (hTP : (∑ j, (K j).conjTranspose * K j) = 1) : 0 ≤ loss K := by
  rw [loss_eq_residual_trace K hTP]
  exact div_nonneg (Finset.sum_nonneg fun j _ => trace_star_self_nonneg (scalarResidual (K j)))
    (Nat.cast_nonneg _)

theorem loss_le_one (K : κ → Matrix ι ι ℂ) : loss K ≤ 1 := by
  apply sub_le_self
  exact div_nonneg (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (sq_nonneg _)

/-- Exact recovery is equivalent to all composed Kraus operators acting as
scalars on the logical system. -/
theorem loss_eq_zero_iff [Nonempty ι] (K : κ → Matrix ι ι ℂ)
    (hTP : (∑ j, (K j).conjTranspose * K j) = 1) :
    loss K = 0 ↔ ∀ j, ∃ z : ℂ, K j = z • (1 : Matrix ι ι ℂ) := by
  have hD : 0 < logicalDim ι := by
    change 0 < (Fintype.card ι : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  rw [loss_eq_residual_trace K hTP, div_eq_zero_iff]
  simp only [hD.ne', or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => trace_star_self_nonneg (scalarResidual (K j)))]
  simp only [Finset.mem_univ, true_implies, trace_star_self_re_eq_zero]
  constructor
  · intro h j
    exact ⟨_, sub_eq_zero.mp (h j)⟩
  · intro h j
    obtain ⟨z, hz⟩ := h j
    have hDc : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι).ne'
    rw [scalarResidual, hz, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      mul_div_cancel_right₀ _ hDc, sub_self]

/-- The unnormalized vector `Σᵢ |i,i⟩` in reference-first tensor order. -/
def bellVector : (ι × ι) → ℂ := fun p => if p.1 = p.2 then 1 else 0

theorem bellVector_overlap (A : Matrix ι ι ℂ) :
    star (bellVector (ι := ι)) ⬝ᵥ
      (((1 : Matrix ι ι ℂ) ⊗ₖ A) *ᵥ bellVector (ι := ι)) = A.trace := by
  have hvec (p : ι × ι) :
      (((1 : Matrix ι ι ℂ) ⊗ₖ A) *ᵥ bellVector (ι := ι)) p = A p.2 p.1 := by
    rcases p with ⟨a, b⟩
    simp [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Matrix.one_apply,
      bellVector, Fintype.sum_prod_type, ite_mul, mul_ite]
  simp [dotProduct, hvec, bellVector, Matrix.trace, Fintype.sum_prod_type, ite_mul]

/-- Maximally entangled reference-input state. -/
def bellProjector (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  (Fintype.card ι : ℂ)⁻¹ • vecMulVec (bellVector (ι := ι)) (star (bellVector (ι := ι)))

/-- The Choi output obtained by applying the channel to only the logical
side of the maximally entangled state. -/
def recoveredChoi (K : κ → Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  ∑ j, ((1 : Matrix ι ι ℂ) ⊗ₖ K j) * bellProjector ι *
    (((1 : Matrix ι ι ℂ) ⊗ₖ K j)).conjTranspose

private theorem conjugateBellProjector (A : Matrix (ι × ι) (ι × ι) ℂ) :
    A * bellProjector ι * A.conjTranspose =
      (Fintype.card ι : ℂ)⁻¹ •
        vecMulVec (A *ᵥ bellVector (ι := ι)) (star (A *ᵥ bellVector (ι := ι))) := by
  simp only [bellProjector, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.star_mulVec]

private theorem bellOverlap_rankOne (v : (ι × ι) → ℂ) :
    star (bellVector (ι := ι)) ⬝ᵥ
      (vecMulVec v (star v) *ᵥ bellVector (ι := ι)) =
      (Complex.normSq (star (bellVector (ι := ι)) ⬝ᵥ v) : ℂ) := by
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, Complex.normSq_eq_conj_mul_self]
  rw [star_dotProduct v (bellVector (ι := ι))]
  change (star (bellVector (ι := ι)) ⬝ᵥ v) * star (star (bellVector (ι := ι)) ⬝ᵥ v) = _
  exact mul_comm _ _

/-- The trace formula agrees with the maximally entangled reference test.
The two factors of the logical dimension come from the normalized initial
state and the normalized test vector. -/
theorem fidelity_eq_bell_overlap (K : κ → Matrix ι ι ℂ) :
    fidelity K =
      (star (bellVector (ι := ι)) ⬝ᵥ
        (recoveredChoi K *ᵥ bellVector (ι := ι))).re / logicalDim ι := by
  simp only [recoveredChoi, conjugateBellProjector, Matrix.sum_mulVec,
    dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
    bellOverlap_rankOne, bellVector_overlap, smul_eq_mul, Complex.re_sum]
  change (∑ j, Complex.normSq (K j).trace) / (logicalDim ι)^2 = _
  have hterm (j : κ) :
      (((Fintype.card ι : ℂ)⁻¹) * (Complex.normSq (K j).trace : ℂ)).re =
        Complex.normSq (K j).trace / logicalDim ι := by
    rw [mul_comm, ← div_eq_mul_inv]
    change ((Complex.normSq (K j).trace : ℂ) / ((logicalDim ι : ℝ) : ℂ)).re = _
    simp
  simp only [hterm, ← Finset.sum_div, ← div_div, pow_two, fidelity]

#print axioms fidelity_eq_bell_overlap
#print axioms loss_eq_residual_trace
#print axioms loss_nonneg
#print axioms loss_le_one
#print axioms loss_eq_zero_iff
#print axioms bellVector_overlap

end
end CriticalDepth.FaultEntanglementFidelity
