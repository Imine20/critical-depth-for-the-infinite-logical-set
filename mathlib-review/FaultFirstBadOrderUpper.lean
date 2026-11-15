import FaultDiamondTail

/-! Exact correction of the histories below the first uncorrectable order
bounds the optimized diamond error by the remaining history mass. -/

namespace CriticalDepth.FaultFirstBadOrder

open Matrix Asymptotics Filter
open CriticalDepth.EncodedFaultRecovery CriticalDepth.IndependentFaultHistories
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultChannelEffects
open CriticalDepth.FaultCPTPRepresentation CriticalDepth.FaultEntanglementFidelity
open scoped BigOperators Topology

noncomputable section

variable {Phys Log : Type*} [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log]

/-- One CPTP recovery corrects the entire finite family when all pairwise
Knill--Laflamme cross terms are scalar. -/
theorem exists_common_cptp_recovery_of_all_scalarCrossTerms
    {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (hscalar : ∀ x y, ∃ z : ℂ,
      (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    ∃ R : RecoveryChannel Phys Log, ∀ x, recoverBranch R.val (A x) = LinearMap.id := by
  obtain ⟨R, hR⟩ := (common_zero_loss_iff A hA).mpr hscalar
  exact ⟨fromKraus R, fun x => recoverBranch_eq_id_of_zero_loss (A x) (hA x) R (hR x)⟩

private theorem channelFidelity_identity :
    channelFidelity (LinearMap.id : MatrixChannel Log Log) = 1 := by
  let K : Fin 1 → Matrix Log Log ℂ := fun _ => 1
  have hId : krausMap K = (LinearMap.id : MatrixChannel Log Log) := by
    apply LinearMap.ext
    intro X
    simp only [krausMap_apply, K, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one, Fin.sum_univ_one, LinearMap.id_apply]
  have hTP : (∑ k, (K k).conjTranspose * K k) = 1 := by
    simp only [K, Matrix.conjTranspose_one, Matrix.one_mul, Fin.sum_univ_one]
  have hLoss := (loss_eq_zero_iff K hTP).mpr (fun k => ⟨1, by simp [K]⟩)
  rw [← hId, channelFidelity_kraus]
  exact (sub_eq_zero.mp hLoss).symm

theorem common_cptp_recovery_iff_scalarCrossTerms
    {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    (∃ R : RecoveryChannel Phys Log, ∀ x, recoverBranch R.val (A x) = LinearMap.id) ↔
      ∀ x y, ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ) := by
  refine ⟨?_, exists_common_cptp_recovery_of_all_scalarCrossTerms A hA⟩
  rintro ⟨R, hR⟩
  obtain ⟨T, rfl⟩ := fromKraus_surjective R
  refine (common_zero_loss_iff A hA).mp ⟨T, ?_⟩
  intro x
  have hLoss := channelBranchLoss_kraus T.kraus (A x)
  change channelBranchLoss (A x) (fromKraus T).val = branchLoss (A x) T at hLoss
  simpa only [channelBranchLoss, hR x, channelFidelity_identity, sub_self] using hLoss.symm

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

private theorem optimalInfidelity_nonneg_of_isometries (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ optimalInfidelity μ A p :=
  FaultExponent.optimalLoss_nonneg μ (fun x R => branchLoss (A x) R)
    (fun x R => (branchLoss_mem_Icc (A x) (hA x) R).1) hp hp₁

private theorem optimalHistoryDiamond_le_tail_of_recovery (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (m : ℕ)
    (R : RecoveryChannel Phys Log)
    (hR : ∀ x, (faults x).card < m → recoverBranch R.val (A x) = LinearMap.id) :
    optimalHistoryDiamond μ A p ≤
      ∑ x ∈ Finset.univ.filter (fun x : History Label => m ≤ (faults x).card), mass μ p x := by
  have hbounded : BddBelow (Set.range fun T : RecoveryChannel Phys Log =>
      halfDiamondByEffects (recoveredHistoryChannel μ A p T)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact Real.sSup_nonneg (by rintro _ ⟨_, _, _, _, _, rfl⟩; exact abs_nonneg _)
  exact (csInf_le hbounded (Set.mem_range_self R)).trans
    (halfDiamond_history_le_tail μ A hA p hp hp₁ m R hR)

theorem optimalHistoryDiamond_le_tail_of_scalarCrossTerms (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (m : ℕ)
    (hscalar : ∀ x y, (faults x).card < m → (faults y).card < m →
      ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    optimalHistoryDiamond μ A p ≤
      ∑ x ∈ Finset.univ.filter (fun x : History Label => m ≤ (faults x).card), mass μ p x := by
  classical
  let Good := {x : History Label // (faults x).card < m}
  let B (x : Good) := A x.val
  obtain ⟨R, hR⟩ := exists_common_cptp_recovery_of_all_scalarCrossTerms B
    (fun x => hA x.val) (fun x y => hscalar x.val y.val x.property y.property)
  exact optimalHistoryDiamond_le_tail_of_recovery μ A hA p hp hp₁ m R
    (fun x hx => hR ⟨x, hx⟩)

theorem optimalHistoryDiamond_isBigO_of_scalarCrossTerms (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (m : ℕ) (hscalar : ∀ x y, (faults x).card < m → (faults y).card < m →
      ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    optimalHistoryDiamond μ A =O[𝓝[>] (0 : ℝ)] fun p => p ^ m := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨((Fintype.card Loc).choose m : ℝ), ?_⟩
  have hp₁ : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, by norm_num, subset_rfl⟩
  filter_upwards [hp₁] with p hp
  have hnonneg : 0 ≤ optimalHistoryDiamond μ A p :=
    (optimalInfidelity_nonneg_of_isometries μ A hA p hp.1.le hp.2.le).trans
      (optimalInfidelity_le_optimalHistoryDiamond μ A hA p hp.1.le hp.2.le)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hp.1.le _)]
  exact (optimalHistoryDiamond_le_tail_of_scalarCrossTerms μ A hA p hp.1.le hp.2.le m
    hscalar).trans (tail μ hp.1.le hp.2.le m)

theorem optimalHistoryDiamond_eq_zero_of_common_cptp_recovery (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (R : RecoveryChannel Phys Log)
    (hR : ∀ x, recoverBranch R.val (A x) = LinearMap.id) :
    optimalHistoryDiamond μ A p = 0 := by
  have hcard (x : History Label) : (faults x).card ≤ Fintype.card Loc :=
    Finset.card_le_univ (faults x)
  have hEmpty :
      Finset.univ.filter (fun x : History Label =>
        Fintype.card Loc + 1 ≤ (faults x).card) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_le_of_gt (Nat.lt_succ_of_le (hcard x))) (Finset.mem_filter.mp hx).2
  have hupper := optimalHistoryDiamond_le_tail_of_recovery μ A hA p hp hp₁
    (Fintype.card Loc + 1) R (fun x _ => hR x)
  rw [hEmpty, Finset.sum_empty] at hupper
  have hnonneg := (optimalInfidelity_nonneg_of_isometries μ A hA p hp hp₁).trans
    (optimalInfidelity_le_optimalHistoryDiamond μ A hA p hp hp₁)
  exact le_antisymm hupper hnonneg

theorem optimalInfidelity_eq_zero_of_common_cptp_recovery (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (R : RecoveryChannel Phys Log)
    (hR : ∀ x, recoverBranch R.val (A x) = LinearMap.id) :
    optimalInfidelity μ A p = 0 := by
  have h := optimalInfidelity_le_optimalHistoryDiamond μ A hA p hp hp₁
  rw [optimalHistoryDiamond_eq_zero_of_common_cptp_recovery μ A hA p hp hp₁ R hR] at h
  exact le_antisymm h (optimalInfidelity_nonneg_of_isometries μ A hA p hp hp₁)

#print axioms exists_common_cptp_recovery_of_all_scalarCrossTerms
#print axioms common_cptp_recovery_iff_scalarCrossTerms
#print axioms optimalHistoryDiamond_le_tail_of_scalarCrossTerms
#print axioms optimalHistoryDiamond_isBigO_of_scalarCrossTerms
#print axioms optimalHistoryDiamond_eq_zero_of_common_cptp_recovery
#print axioms optimalInfidelity_eq_zero_of_common_cptp_recovery

end

end CriticalDepth.FaultFirstBadOrder
