import FaultHaarOptimality
import FaultDiamondIdealAction

/-!
Haar average of the actual recovered channel and invariance under undoing the
ideal logical gate.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open Matrix CriticalDepth.Manuscript
open CriticalDepth.FaultChannelEffects
open CriticalDepth.FaultEntanglementFidelity CriticalDepth.FaultCPTPRepresentation
open CriticalDepth.FaultCPTPOptimality CriticalDepth.IndependentFaultHistories
open scoped BigOperators

variable {Phys Log Loc : Type*} [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

/-- Averaging over histories is the Haar infidelity of the one recovered
mixture channel, by the affine fidelity identity. -/
theorem channelAverageHistoryLoss_eq_recoveredHistoryChannel (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (R : RecoveryChannel Phys Log) :
    channelAverageHistoryLoss μ A p R =
      channelAverageInfidelity (recoveredHistoryChannel μ A p R) := by
  rw [channelAverageHistoryLoss_eq_dim_ratio_loss μ A hA p R, history_loss_eq_one_sub_fidelity]
  exact (channelAverageInfidelity_eq_dim_ratio_fidelity
    ⟨_, historyChannel_isCPTP μ A hA p hp hp₁ R⟩).symm

private theorem conjugated_krausMap {Rec : Type*} [Fintype Rec]
    (T : Rec → Matrix Log Log ℂ) (U : Operator Log) :
    (conjugateChannel U.conjTranspose).comp ((krausMap T).comp (conjugateChannel U)) =
      krausMap (fun k => U.conjTranspose * T k * U) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, krausMap_apply, conjugateChannel, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

private theorem trace_conjugated (U : Operator Log) (hU : IsUnitary U) (A : Operator Log) :
    (U.conjTranspose * A * U).trace = A.trace := by
  have hu : U * U.conjTranspose = 1 := hU.2
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]

private theorem complete_conjugated {Rec : Type*} [Fintype Rec]
    (T : Rec → Matrix Log Log ℂ) (hT : ∑ k, (T k).conjTranspose * T k = 1)
    (U : Operator Log) (hU : IsUnitary U) :
    ∑ k, (U.conjTranspose * T k * U).conjTranspose * (U.conjTranspose * T k * U) = 1 := by
  have hU₁ : U.conjTranspose * U = 1 := hU.1
  have hU₂ : U * U.conjTranspose = 1 := hU.2
  calc
    _ = ∑ k, U.conjTranspose * ((T k).conjTranspose * (T k)) * U := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      have hh : (U.conjTranspose * ((T k).conjTranspose * U)) *
          (U.conjTranspose * T k * U) =
          U.conjTranspose * ((T k).conjTranspose * (U * U.conjTranspose) * T k) * U := by
        noncomm_ring
      rw [hh, hU₂, Matrix.mul_one]
    _ = U.conjTranspose * (∑ k, (T k).conjTranspose * T k) * U := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = 1 := by rw [hT, Matrix.mul_one, hU₁]

theorem channelAverageInfidelity_conjugateChannel
    (L : RecoveryChannel Log Log) (U : Operator Log) (hU : IsUnitary U) :
    channelAverageInfidelity
      ((conjugateChannel U.conjTranspose).comp (L.val.comp (conjugateChannel U))) =
        channelAverageInfidelity L.val := by
  obtain ⟨K, hK, hTP⟩ := (cptp_iff_exists_completeKraus L.val).mp L.property
  let K' := fun k => U.conjTranspose * K k * U
  let L' : RecoveryChannel Log Log := ⟨krausMap K', kraus_isCompletelyPositive _,
    (kraus_isTracePreserving_iff _).mpr (complete_conjugated K hTP U hU)⟩
  have hUeq :
      (conjugateChannel U.conjTranspose).comp (L.val.comp (conjugateChannel U)) = L'.val := by
    rw [hK, conjugated_krausMap]
  have hF : channelFidelity L'.val = channelFidelity L.val := by
    have hh : L'.val = krausMap K' := rfl
    rw [hh, hK, channelFidelity_kraus, channelFidelity_kraus]
    simp only [fidelity, K', trace_conjugated U hU]
  rw [hUeq, channelAverageInfidelity_eq_dim_ratio_fidelity L',
    channelAverageInfidelity_eq_dim_ratio_fidelity L, hF]

theorem channelAverageHistoryLoss_eq_undoIdeal (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (R : RecoveryChannel Phys Log)
    (W : Operator Log) (hW : IsUnitary W) :
    channelAverageHistoryLoss μ A p R = channelAverageInfidelity (undoIdealHistoryChannel μ A p R W) := by
  rw [undoIdealHistoryChannel_eq, channelAverageHistoryLoss_eq_recoveredHistoryChannel μ A hA p hp hp₁ R]
  exact (channelAverageInfidelity_conjugateChannel
    ⟨_, historyChannel_isCPTP μ A hA p hp hp₁ R⟩ W hW).symm

theorem optimalAverageInfidelity_eq_undoIdeal (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (W : Operator Log) (hW : IsUnitary W) :
    optimalAverageInfidelity μ A p =
      sInf (Set.range fun R => channelAverageInfidelity (undoIdealHistoryChannel μ A p R W)) := by
  unfold optimalAverageInfidelity
  congr 1
  apply congrArg Set.range
  funext R
  exact channelAverageHistoryLoss_eq_undoIdeal μ A hA p hp hp₁ R W hW

#print axioms channelAverageHistoryLoss_eq_recoveredHistoryChannel
#print axioms channelAverageInfidelity_conjugateChannel
#print axioms optimalAverageInfidelity_eq_undoIdeal

end
end CriticalDepth.FaultAverageInfidelity
