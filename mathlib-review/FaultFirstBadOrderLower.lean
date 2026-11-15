import EncodedFaultRecovery
import FaultKrausCompression

/-!
The first uncorrectable fault order gives a positive entanglement loss
uniformly over terminal recoveries for the selected low-order histories.
-/

namespace CriticalDepth.FaultFirstBadOrder

noncomputable section

open Filter Set
open scoped BigOperators Topology
open CriticalDepth.EncodedFaultRecovery CriticalDepth.FaultEntanglementFidelity
open CriticalDepth.FaultKrausCompactness CriticalDepth.FaultProbability
open CriticalDepth.IndependentFaultHistories CriticalDepth.Manuscript20261114

variable {Phys Log : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]

private theorem uniform_loss_of_failed_crossTerms {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (histories : Finset Hist)
    (hbad : ¬ ∀ x ∈ histories, ∀ y ∈ histories,
      ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    ∃ b : ℝ, 0 < b ∧ ∀ T : TerminalRecovery Phys Log, b ≤ ∑ x ∈ histories, branchLoss (A x) T := by
  classical
  obtain ⟨S, hS, hmin⟩ := FaultKrausCompression.exists_minimum_all_finiteKraus
    histories (fun _ => (1 : ℝ)) A
  let e := Fintype.equivFin (Log × Phys)
  have hComplete : (∑ k, (S (e.symm k)).conjTranspose * S (e.symm k)) = 1 :=
    (e.symm.sum_comp (fun k => (S k).conjTranspose * S k)).trans hS
  let R : TerminalRecovery Phys Log := ⟨_, S ∘ e.symm, hComplete⟩
  have hRloss (x : Hist) : branchLoss (A x) R = loss (fun k => S k * A x) := by
    have hsum : (∑ k, Complex.normSq ((R.kraus k * A x).trace)) =
        ∑ k, Complex.normSq ((S k * A x).trace) :=
      e.symm.sum_comp (fun k => Complex.normSq ((S k * A x).trace))
    unfold branchLoss loss fidelity
    rw [hsum]
  have hnonneg (x : Hist) : 0 ≤ branchLoss (A x) R :=
    (branchLoss_mem_Icc (A x) (hA x) R).1
  have hpositive : 0 < ∑ x ∈ histories, branchLoss (A x) R := by
    by_contra! hzero
    have hexact (x : ↥histories) : branchLoss (A x.val) R = 0 := by
      have hx := Finset.single_le_sum (s := histories)
        (f := fun z => branchLoss (A z) R) (fun z _ => hnonneg z) x.property
      exact le_antisymm (hx.trans hzero) (hnonneg x.val)
    have hscalar := (common_zero_loss_iff (fun x : ↥histories => A x.val)
      (fun x => hA x.val)).mp ⟨R, hexact⟩
    apply hbad
    intro x hx y hy
    exact hscalar ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨_, hpositive, fun T => ?_⟩
  calc
    ∑ x ∈ histories, branchLoss (A x) R = ∑ x ∈ histories, loss (fun k => S k * A x) :=
      Finset.sum_congr rfl (fun x _ => hRloss x)
    _ ≤ ∑ x ∈ histories, branchLoss (A x) T := by
      simpa only [one_mul, branchLoss] using hmin T.count T.kraus T.complete

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

/-- Failure of joint exact recovery on the histories through order m
gives an order-m lower bound even for a recovery chosen as a function of
the fault rate. -/
theorem optimalInfidelity_eventual_powerLower_of_bad_order (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (m : ℕ) (hbad : ¬ ∀ x y, (faults x).card ≤ m → (faults y).card ≤ m →
      ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ), c * p ^ m ≤ optimalInfidelity μ A p := by
  classical
  let low := Finset.univ.filter (fun x : History Label => (faults x).card ≤ m)
  obtain ⟨b, hb, hloss⟩ := uniform_loss_of_failed_crossTerms A hA low (by
    intro h
    apply hbad
    intro x y hx hy
    exact h x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
      y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩))
  let coefficient (x : History Label) : ℝ :=
    conditionalWeight μ x * (1 / 2 : ℝ) ^ (Fintype.card Loc - (faults x).card)
  have hCoefficient (x : History Label) : 0 < coefficient x :=
    mul_pos (conditionalWeight_pos μ x) (pow_pos (by norm_num) _)
  let C : ℝ := 1 + ∑ x : History Label, 1 / coefficient x
  have hC : 0 < C := by
    have hn : 0 ≤ ∑ x : History Label, 1 / coefficient x :=
      Finset.sum_nonneg (fun x _ => div_nonneg zero_le_one (hCoefficient x).le)
    unfold C
    linarith
  have hUniform (x : History Label) : 1 / C ≤ coefficient x := by
    have hx : 1 / coefficient x ≤ ∑ y : History Label, 1 / coefficient y :=
      Finset.single_le_sum (fun y _ => div_nonneg zero_le_one (hCoefficient y).le) (Finset.mem_univ x)
    have h : 1 / coefficient x ≤ C := by unfold C; linarith
    exact (div_le_iff₀ hC).mpr (by
      simpa only [mul_comm] using (div_le_iff₀ (hCoefficient x)).mp h)
  refine ⟨(1 / C) * b, mul_pos (div_pos zero_lt_one hC) hb, ?_⟩
  have hhalf : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_, by norm_num, subset_rfl⟩
  filter_upwards [hhalf] with p hp
  have hpOne : p ≤ 1 := by linarith [hp.2]
  have hMass (x : History Label) (hx : x ∈ low) : (1 / C) * p ^ m ≤ mass μ p x := by
    have hxm : (faults x).card ≤ m := (Finset.mem_filter.mp hx).2
    rw [mass_eq_historyMass]
    exact (mul_le_mul (hUniform x) (pow_le_pow_of_le_one hp.1.le hpOne hxm)
      (pow_nonneg hp.1.le _) (hCoefficient x).le).trans
      (historyMassBounds p (conditionalWeight μ x) (faults x).card
        (Fintype.card Loc - (faults x).card) hp.1.le hp.2.le (conditionalWeight_pos μ x).le).1
  unfold optimalInfidelity FaultExponent.optimalLoss
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨R, rfl⟩
  calc
    ((1 / C) * b) * p ^ m = ((1 / C) * p ^ m) * b := mul_right_comm ..
    _ ≤ FaultExponent.lossAt μ (fun x => branchLoss (A x)) p R :=
      expectedHistoryLoss_ge_weightedSubset (Finset.subset_univ low) (mass μ p)
        (fun x => branchLoss (A x) R) (mul_nonneg (div_pos zero_lt_one hC).le (pow_nonneg hp.1.le _))
        (fun x _ => mass_nonneg μ hp.1.le hpOne x)
        (fun x _ => (branchLoss_mem_Icc (A x) (hA x) R).1) hMass (hloss R)

#print axioms optimalInfidelity_eventual_powerLower_of_bad_order

end
end CriticalDepth.FaultFirstBadOrder
