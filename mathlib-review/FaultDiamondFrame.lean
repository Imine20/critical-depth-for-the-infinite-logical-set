import FaultDiamondEffects
import CriticalDepthMathlib

/-!
The half diamond distance to identity is unchanged by a change of logical frame.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.Manuscript CriticalDepth.FaultCPTPRepresentation
open scoped Kronecker ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conjugateChannel (U : Operator ι) : MatrixChannel ι ι where
  toFun A := U * A * U.conjTranspose
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' z A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

theorem amplify_comp {ν σ Ref : Type*} [Fintype ν] [DecidableEq ν]
    [Fintype σ] [DecidableEq σ]
    (L : MatrixChannel ν σ) (M : MatrixChannel ι ν) (X : Matrix (Ref × ι) (Ref × ι) ℂ) :
    amplify (L.comp M) X = amplify L (amplify M X) := by
  ext p q
  rfl

theorem amplify_conjugateChannel {R : Type*} [Fintype R] [DecidableEq R]
    (U : Operator ι) (A : Matrix (R × ι) (R × ι) ℂ) :
    amplify (conjugateChannel U) A =
      ((1 : Matrix R R ℂ) ⊗ₖ U) * A * ((1 : Matrix R R ℂ) ⊗ₖ U).conjTranspose := by
  have hChannel : conjugateChannel U = krausMap (fun _ : Unit => U) := by
    ext X i j
    simp [conjugateChannel, krausMap_apply]
  rw [hChannel, amplify_kraus]
  simp

theorem channelEffectValue_conjugate {R : Type*} [Fintype R] [DecidableEq R]
    (U : Operator ι) (hU : IsUnitary U)
    (L : MatrixChannel ι ι) (A E : Matrix (R × ι) (R × ι) ℂ) :
    let V := (1 : Matrix R R ℂ) ⊗ₖ U
    effectValue E (amplify ((conjugateChannel U.conjTranspose).comp (L.comp (conjugateChannel U))) A - A) =
      effectValue (V * E * V.conjTranspose) (amplify L (V * A * V.conjTranspose) - V * A * V.conjTranspose) := by
  intro V
  have hv : V.conjTranspose * V = 1 ∧ V * V.conjTranspose = 1 :=
    point_kronecker_isUnitary _ _ isUnitary_one hU
  have hstar : ((1 : Matrix R R ℂ) ⊗ₖ U.conjTranspose) = V.conjTranspose := by
    simp [V, Matrix.conjTranspose_kronecker]
  simp only [amplify_comp, amplify_conjugateChannel, hstar, Matrix.conjTranspose_conjTranspose]
  rw [effectValue_sub, effectValue_sub]
  congr 1
  · unfold effectValue
    apply congrArg Complex.re
    let B := amplify L (V * A * V.conjTranspose)
    change (E * (V.conjTranspose * B * V)).trace = (V * E * V.conjTranspose * B).trace
    rw [show E * (V.conjTranspose * B * V) = (E * V.conjTranspose * B) * V by noncomm_ring,
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  · unfold effectValue
    apply congrArg Complex.re
    symm
    calc
      _ = (V * E * (V.conjTranspose * V) * A * V.conjTranspose).trace := by
        congr 1
        noncomm_ring
      _ = (V * E * A * V.conjTranspose).trace := by rw [hv.1, Matrix.mul_one]
      _ = (V.conjTranspose * V * E * A).trace := by
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hv.1, Matrix.one_mul]

theorem halfDiamondByEffects_conjugateChannel_le (U : Operator ι) (hU : IsUnitary U)
    (L : MatrixChannel ι ι) (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L) :
    halfDiamondByEffects ((conjugateChannel U.conjTranspose).comp (L.comp (conjugateChannel U))) ≤
      halfDiamondByEffects L := by
  unfold halfDiamondByEffects
  apply real_sSup_le_of_nonneg
  · rintro _ ⟨m, A, E, hA, hE, rfl⟩
    let V := (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U
    have hv : V.conjTranspose * V = 1 ∧ V * V.conjTranspose = 1 :=
      point_kronecker_isUnitary _ _ isUnitary_one hU
    have hDensity : IsDensity (V * A * V.conjTranspose) := by
      refine ⟨hA.1.mul_mul_conjTranspose_same V, ?_⟩
      rw [Matrix.trace_mul_cycle, hv.1, Matrix.one_mul, hA.2]
    have hEffect : IsEffect (V * E * V.conjTranspose) := by
      refine ⟨hE.1.mul_mul_conjTranspose_same V, ?_⟩
      have he : 1 - V * E * V.conjTranspose = V * (1 - E) * V.conjTranspose := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hv.2]
      rw [he]
      exact hE.2.mul_mul_conjTranspose_same V
    rw [channelEffectValue_conjugate U hU L A E]
    exact effect_test_le_halfDiamond L hCP hTP m _ _ hDensity hEffect
  · apply Real.sSup_nonneg
    rintro _ ⟨_, _, _, _, _, rfl⟩
    exact abs_nonneg _

theorem halfDiamondByEffects_conjugateChannel (U : Operator ι) (hU : IsUnitary U)
    (L : MatrixChannel ι ι) (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L) :
    halfDiamondByEffects ((conjugateChannel U.conjTranspose).comp (L.comp (conjugateChannel U))) =
      halfDiamondByEffects L := by
  let M := (conjugateChannel U.conjTranspose).comp (L.comp (conjugateChannel U))
  have hU₁ : U.conjTranspose * U = 1 := hU.1
  have hU₂ : U * U.conjTranspose = 1 := hU.2
  have hV : IsUnitary U.conjTranspose := by
    change U.conjTranspose.conjTranspose * U.conjTranspose = 1 ∧
      U.conjTranspose * U.conjTranspose.conjTranspose = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact ⟨hU₂, hU₁⟩
  have hCPM : IsCompletelyPositive M := by
    intro m X hX
    dsimp only [M]
    simp only [amplify_comp, amplify_conjugateChannel]
    exact (hCP m _ (hX.mul_mul_conjTranspose_same _)).mul_mul_conjTranspose_same _
  have hTPM : IsTracePreserving M := by
    intro X
    dsimp [M, conjugateChannel]
    rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_cycle, hU₂, Matrix.one_mul,
      hTP, Matrix.trace_mul_cycle, hU₁, Matrix.one_mul]
  have hUndo : (conjugateChannel U.conjTranspose.conjTranspose).comp
      (M.comp (conjugateChannel U.conjTranspose)) = L := by
    ext A i j
    simp only [M, LinearMap.comp_apply, conjugateChannel, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.conjTranspose_conjTranspose]
    have hAux (X : Operator ι) : U * (U.conjTranspose * X * U) * U.conjTranspose = X := by
      calc
        _ = (U * U.conjTranspose) * X * (U * U.conjTranspose) := by noncomm_ring
        _ = _ := by rw [hU₂, Matrix.one_mul, Matrix.mul_one]
    rw [hAux, hAux]
  apply le_antisymm (halfDiamondByEffects_conjugateChannel_le U hU L hCP hTP)
  have h := halfDiamondByEffects_conjugateChannel_le U.conjTranspose hV M hCPM hTPM
  rw [hUndo] at h
  exact h

#print axioms halfDiamondByEffects_conjugateChannel

end
end CriticalDepth.FaultChannelEffects
