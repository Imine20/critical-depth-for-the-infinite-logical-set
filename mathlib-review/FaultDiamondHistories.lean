import FaultBellEffect

/-!
Operational diamond error of a mixture over independent unobserved histories.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix Asymptotics Filter
open CriticalDepth.FaultCPTPRepresentation CriticalDepth.FaultCPTPOptimality
open CriticalDepth.FaultEntanglementFidelity CriticalDepth.EncodedFaultRecovery
open CriticalDepth.IndependentFaultHistories
open scoped BigOperators ComplexOrder Kronecker ENat Topology

noncomputable section

variable {Phys Log Loc : Type*} [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

def recoveredHistoryChannel (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (p : ℝ) (R : RecoveryChannel Phys Log) : MatrixChannel Log Log :=
  ∑ x, ((mass μ p x : ℝ) : ℂ) • recoverBranch R.val (A x)

theorem recoverBranch_isCPTP (A : Matrix Phys Log ℂ) (hA : A.conjTranspose * A = 1)
    (R : RecoveryChannel Phys Log) :
    IsCompletelyPositive (recoverBranch R.val A) ∧ IsTracePreserving (recoverBranch R.val A) := by
  obtain ⟨T, rfl⟩ := fromKraus_surjective R
  rw [show (fromKraus T).val = krausMap T.kraus from rfl, recoverBranch_kraus]
  exact ⟨kraus_isCompletelyPositive _, (kraus_isTracePreserving_iff _).mpr (composed_complete A hA T)⟩

theorem amplify_sum {β Ref : Type*} [Fintype β] (s : Finset β) (F : β → MatrixChannel Log Log)
    (X : Matrix (Ref × Log) (Ref × Log) ℂ) :
    amplify (∑ b ∈ s, F b) X = ∑ b ∈ s, amplify (F b) X := by
  classical
  induction s using Finset.induction_on with
  | empty => ext p q; simp [amplify]
  | @insert b s hb ih => rw [Finset.sum_insert hb, amplify_add, ih, Finset.sum_insert hb]

theorem historyChannel_isCPTP (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (R : RecoveryChannel Phys Log) :
    IsCompletelyPositive (recoveredHistoryChannel μ A p R) ∧
      IsTracePreserving (recoveredHistoryChannel μ A p R) := by
  have hB (x : History Label) := recoverBranch_isCPTP (A x) (hA x) R
  constructor
  · intro n X hX
    unfold recoveredHistoryChannel
    rw [amplify_sum]
    apply Matrix.posSemidef_sum
    intro x _
    rw [amplify_smul]
    exact (hB x).1 n X hX |>.smul (by
      exact Complex.nonneg_iff.mpr ⟨by simpa using mass_nonneg μ hp hp₁ x, by simp⟩)
  · intro X
    simp only [recoveredHistoryChannel, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    have h : (∑ x, (mass μ p x : ℂ)) = 1 := by
      exact_mod_cast sum_mass μ p
    calc
      _ = ∑ x, (mass μ p x : ℂ) * X.trace := by
        apply Finset.sum_congr rfl
        intro x _
        have ht : ((recoverBranch R.val (A x)) X).trace = X.trace := (hB x).2 X
        rw [ht]
      _ = X.trace := by rw [← Finset.sum_mul, h, one_mul]

theorem history_loss_eq_one_sub_fidelity (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (p : ℝ) (R : RecoveryChannel Phys Log) :
    channelHistoryLoss μ A p R = 1 - channelFidelity (recoveredHistoryChannel μ A p R) := by
  unfold channelHistoryLoss channelBranchLoss channelFidelity recoveredHistoryChannel
  rw [amplify_sum]
  simp only [amplify_smul, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    smul_eq_mul, Finset.sum_div, mul_sub, mul_one, Finset.sum_sub_distrib, sum_mass]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

def optimalHistoryDiamond (μ : Law Label) (A : History Label → Matrix Phys Log ℂ) (p : ℝ) : ℝ :=
  sInf (Set.range fun R : RecoveryChannel Phys Log => halfDiamondByEffects (recoveredHistoryChannel μ A p R))

theorem optimalInfidelity_le_optimalHistoryDiamond (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    optimalInfidelity μ A p ≤ optimalHistoryDiamond μ A p := by
  obtain ⟨R₀, hR₀⟩ := exists_cptp_optimalInfidelity μ A p
  apply le_csInf ⟨_, Set.mem_range_self R₀⟩
  rintro _ ⟨R, rfl⟩
  have hb : BddBelow (Set.range (channelHistoryLoss μ A p)) := by
    use 0
    rintro _ ⟨T, rfl⟩
    obtain ⟨K, rfl⟩ := fromKraus_surjective T
    rw [channelHistoryLoss_eq_kraus]
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (mass_nonneg μ hp hp₁ x) (branchLoss_mem_Icc (A x) (hA x) K).1
  have hOpt : optimalInfidelity μ A p ≤ channelHistoryLoss μ A p R := by
    rw [optimalInfidelity_eq_cptp_inf]
    exact csInf_le hb (Set.mem_range_self R)
  have h := historyChannel_isCPTP μ A hA p hp hp₁ R
  rw [history_loss_eq_one_sub_fidelity] at hOpt
  exact hOpt.trans (loss_le_halfDiamond _ h.1 h.2)

#print axioms optimalInfidelity_le_optimalHistoryDiamond

end

end CriticalDepth.FaultChannelEffects