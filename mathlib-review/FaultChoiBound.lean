import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Two orthogonal tests on a recovered Choi state

A positive semidefinite state of trace one has total overlap at most one
with two orthonormal vectors. The fault-history application also requires
a channel calculation identifying the two target Choi vectors.
-/

namespace CriticalDepth.FaultChoiBound

noncomputable section

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def projector (v : ι → ℂ) : Matrix ι ι ℂ := vecMulVec v (star v)

private theorem projector_mul (v w : ι → ℂ) :
    projector v * projector w = vecMulVec v ((star v ⬝ᵥ w) • star w) := by
  exact vecMulVec_mul_vecMulVec _ _ _ _

private theorem projector_adjoint (v : ι → ℂ) :
    (projector v).conjTranspose = projector v := by
  simp only [projector, conjTranspose_vecMulVec, star_star]

private theorem projector_trace (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    (A * projector v).trace = star v ⬝ᵥ (A *ᵥ v) := by
  rw [projector, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- The trace of the complementary positive compression bounds the sum of
the two pure-state overlaps. -/
theorem orthogonalOverlaps_le_trace (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (v w : ι → ℂ) (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1)
    (hvw : star v ⬝ᵥ w = 0) :
    (star v ⬝ᵥ (A *ᵥ v)).re + (star w ⬝ᵥ (A *ᵥ w)).re ≤ A.trace.re := by
  have hwv : star w ⬝ᵥ v = 0 := by
    rw [star_dotProduct w v, hvw, star_zero]
  let P := projector v + projector w
  let Q := 1 - P
  have hPstar : P.conjTranspose = P := by
    simp only [P, conjTranspose_add, projector_adjoint]
  have hpv : projector v * projector v = projector v := by
    simpa only [hv, one_smul, projector] using projector_mul v v
  have hpw : projector w * projector w = projector w := by
    simpa only [hw, one_smul, projector] using projector_mul w w
  have hpvw : projector v * projector w = 0 := by
    rw [projector_mul, hvw, zero_smul]
    ext i j
    simp [vecMulVec]
  have hpwv : projector w * projector v = 0 := by
    rw [projector_mul, hwv, zero_smul]
    ext i j
    simp [vecMulVec]
  have hPmul : P * P = P := by
    simp only [P, Matrix.add_mul, Matrix.mul_add, hpv, hpw, hpvw, hpwv, zero_add, add_zero]
  have hQstar : Q.conjTranspose = Q := by
    simp only [Q, conjTranspose_sub, conjTranspose_one, hPstar]
  have hQmul : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hPmul, sub_self, sub_zero]
  have hpos : (Q * A * Q).PosSemidef := by
    simpa only [hQstar] using hA.mul_mul_conjTranspose_same Q
  have ht : (Q * A * Q).trace = A.trace -
      ((star v ⬝ᵥ (A *ᵥ v)) + (star w ⬝ᵥ (A *ᵥ w))) := by
    rw [trace_mul_cycle Q A Q, hQmul]
    rw [trace_mul_comm Q A]
    simp only [Q, P, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add, trace_sub,
      trace_add, projector_trace]
  have htrace := hpos.trace_nonneg
  rw [ht] at htrace
  have hr := (Complex.nonneg_iff.mp htrace).1
  simp only [Complex.sub_re, Complex.add_re] at hr
  linarith

theorem orthogonalOverlaps_le_one (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (htrace : A.trace = 1) (v w : ι → ℂ)
    (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1) (hvw : star v ⬝ᵥ w = 0) :
    (star v ⬝ᵥ (A *ᵥ v)).re + (star w ⬝ᵥ (A *ᵥ w)).re ≤ 1 := by
  simpa only [htrace, Complex.one_re] using orthogonalOverlaps_le_trace A hA v w hv hw hvw

example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (star (![1, 0] : Fin 2 → ℂ) ⬝ᵥ (A *ᵥ ![1, 0])).re +
      (star (![0, 1] : Fin 2 → ℂ) ⬝ᵥ (A *ᵥ ![0, 1])).re ≤ 1 := by
  exact orthogonalOverlaps_le_one A hA htrace ![1, 0] ![0, 1]
    (by simp [dotProduct, Fin.sum_univ_two]) (by simp [dotProduct, Fin.sum_univ_two])
    (by simp [dotProduct, Fin.sum_univ_two])

#print axioms orthogonalOverlaps_le_trace
#print axioms orthogonalOverlaps_le_one

end

end CriticalDepth.FaultChoiBound
