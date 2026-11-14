import FaultDiamondEffects
import FaultCPTPOptimality

/-!
The maximally entangled state and its projector form an admissible
distinguishing test for a residual logical channel.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.FaultCPTPRepresentation CriticalDepth.FaultCPTPOptimality
open CriticalDepth.FaultEntanglementFidelity
open scoped BigOperators ComplexOrder Kronecker

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem bellVector_normSq : (star (bellVector (ι := ι))) ⬝ᵥ bellVector = (Fintype.card ι : ℂ) := by
  simpa only [Matrix.one_kronecker_one, Matrix.one_mulVec, Matrix.trace_one] using
    bellVector_overlap (1 : Matrix ι ι ℂ)

private theorem bell_density_trace : (bellProjector ι).trace = 1 := by
  have hD : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι).ne'
  rw [bellProjector, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm, bellVector_normSq]
  exact inv_mul_cancel₀ hD

private theorem bell_hermitian : (bellProjector ι).IsHermitian := by
  change (bellProjector ι).conjTranspose = bellProjector ι
  unfold bellProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
  simp

private theorem bell_idempotent : bellProjector ι * bellProjector ι = bellProjector ι := by
  have hD : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι).ne'
  unfold bellProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
    smul_smul, bellVector_normSq, Matrix.vecMulVec_smul]
  rw [inv_mul_cancel₀ hD, mul_one]

theorem bell_isDensity : IsDensity (bellProjector ι) :=
  ⟨(projector_isEffect _ bell_hermitian bell_idempotent).1, bell_density_trace⟩

theorem bell_effectValue (A : Matrix (ι × ι) (ι × ι) ℂ) :
    effectValue (bellProjector ι) A =
      (star (bellVector (ι := ι)) ⬝ᵥ (A *ᵥ bellVector)).re / (Fintype.card ι : ℝ) := by
  unfold effectValue bellProjector
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm (vecMulVec _ _),
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  change (((Fintype.card ι : ℂ)⁻¹) * _).re = _
  rw [mul_comm, ← div_eq_mul_inv]
  change (_ / ((Fintype.card ι : ℝ) : ℂ)).re = _
  simp [Complex.div_ofReal_re]

theorem loss_le_halfDiamond (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L) :
    1 - channelFidelity L ≤ halfDiamondByEffects L := by
  let E := Fintype.equivFin ι
  let e : Fin (Fintype.card ι) × ι ≃ ι × ι := E.symm.prodCongr (Equiv.refl ι)
  let P : Matrix (Fin (Fintype.card ι) × ι) (Fin (Fintype.card ι) × ι) ℂ :=
    (bellProjector ι).submatrix e e
  have htrace (A : Matrix (ι × ι) (ι × ι) ℂ) : (A.submatrix e e).trace = A.trace :=
    Fintype.sum_equiv e _ _ fun _ => rfl
  have hPos : IsDensity P := ⟨(bell_isDensity (ι := ι)).1.submatrix e, by change ((bellProjector ι).submatrix e e).trace = 1; rw [htrace, bell_density_trace]⟩
  have hOne : (1 : Matrix (ι × ι) (ι × ι) ℂ).submatrix e e = 1 := Matrix.submatrix_one_equiv e
  have hEff : IsEffect P := by
    have h := projector_isEffect (bellProjector ι) bell_hermitian bell_idempotent
    refine ⟨h.1.submatrix e, ?_⟩
    have hh := h.2.submatrix e
    change ((1 - bellProjector ι).submatrix e e).PosSemidef at hh
    change ((1 : Matrix (ι × ι) (ι × ι) ℂ).submatrix e e - P).PosSemidef at hh
    rwa [hOne] at hh
  have hEval :
      amplify L P - P = (amplify L (bellProjector ι) - bellProjector ι).submatrix e e := by
    ext p q
    rfl
  have hVal :
      effectValue P (amplify L P - P) = effectValue (bellProjector ι)
        (amplify L (bellProjector ι) - bellProjector ι) := by
    rw [hEval, effectValue, effectValue]
    dsimp only [P]
    rw [Matrix.submatrix_mul_equiv, htrace]
  have h := effect_test_le_halfDiamond L hCP hTP _ P P hPos hEff
  rw [hVal, effectValue_sub, bell_effectValue (amplify L (bellProjector ι))] at h
  have hPP : effectValue (bellProjector ι) (bellProjector ι) = 1 := by
    rw [effectValue, bell_idempotent, bell_density_trace, Complex.one_re]
  rw [hPP] at h
  change |channelFidelity L - 1| ≤ halfDiamondByEffects L at h
  have hneg := (neg_le_abs (channelFidelity L - 1)).trans h
  linarith

#print axioms bell_isDensity
#print axioms loss_le_halfDiamond

end

end CriticalDepth.FaultChannelEffects