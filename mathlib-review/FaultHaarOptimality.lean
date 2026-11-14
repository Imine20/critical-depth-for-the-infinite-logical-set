import FaultHaarChannelFidelity
import Mathlib.Basic.Real.Pointwise

/-! The optimal Haar-averaged loss and exponent of an encoded fault experiment. -/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open Matrix Asymptotics Filter
open CriticalDepth.FaultCPTPOptimality CriticalDepth.EncodedFaultRecovery
open CriticalDepth.IndependentFaultHistories
open scoped BigOperators Topology ENat

variable {Phys Log : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

/-- The pure-state average of a common recovered mixture of encoded histories. -/
def channelAverageHistoryLoss (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (p : ℝ) (L : RecoveryChannel Phys Log) : ℝ :=
  ∑ x, mass μ p x * channelAverageInfidelity (recoverBranch L.val (A x))

theorem channelAverageHistoryLoss_eq_dim_ratio_loss
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) (p : ℝ) (R : RecoveryChannel Phys Log) :
    channelAverageHistoryLoss μ A p R = fidelityDimensionRatio Log * channelHistoryLoss μ A p R := by
  unfold channelAverageHistoryLoss channelHistoryLoss
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [channelAverageBranch_eq_dim_ratio_loss R (A x) (hA x)]
  ring

def optimalAverageInfidelity (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (p : ℝ) : ℝ := sInf (Set.range (channelAverageHistoryLoss μ A p))

theorem optimalAverageInfidelity_eq_dim_ratio
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) (p : ℝ) :
    optimalAverageInfidelity μ A p = fidelityDimensionRatio Log * optimalInfidelity μ A p := by
  rw [optimalInfidelity_eq_cptp_inf]
  unfold optimalAverageInfidelity
  change (⨅ R : RecoveryChannel Phys Log, channelAverageHistoryLoss μ A p R) =
    fidelityDimensionRatio Log • (⨅ R : RecoveryChannel Phys Log, channelHistoryLoss μ A p R)
  rw [Real.smul_iInf_of_nonneg (fidelityDimensionRatio_pos Log).le]
  apply iInf_congr
  intro R
  exact channelAverageHistoryLoss_eq_dim_ratio_loss μ A hA p R

theorem channelAverageHistoryLoss_is_optimal_iff
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) (p : ℝ) (R : RecoveryChannel Phys Log) :
    channelAverageHistoryLoss μ A p R = optimalAverageInfidelity μ A p ↔
      channelHistoryLoss μ A p R = optimalInfidelity μ A p := by
  rw [channelAverageHistoryLoss_eq_dim_ratio_loss μ A hA p R,
    optimalAverageInfidelity_eq_dim_ratio μ A hA p]
  exact ⟨mul_left_cancel₀ (fidelityDimensionRatio_pos Log).ne',
    congrArg (fun x => fidelityDimensionRatio Log * x)⟩

theorem optimalAverageInfidelity_exponent_eq
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    FaultExponent.exponent (optimalAverageInfidelity μ A) =
      FaultExponent.exponent (optimalInfidelity μ A) := by
  have heq : optimalAverageInfidelity μ A =
      fun p => fidelityDimensionRatio Log * optimalInfidelity μ A p :=
    funext (optimalAverageInfidelity_eq_dim_ratio μ A hA)
  rw [heq]
  unfold FaultExponent.exponent
  apply congrArg sSup
  ext k
  simp only [Set.mem_setOf_eq, Asymptotics.isBigO_const_mul_left_iff
    (fidelityDimensionRatio_pos Log).ne']

#print axioms channelAverageInfidelity_eq_dim_ratio_fidelity
#print axioms optimalAverageInfidelity_eq_dim_ratio
#print axioms channelAverageHistoryLoss_is_optimal_iff
#print axioms optimalAverageInfidelity_exponent_eq

end
end CriticalDepth.FaultAverageInfidelity
