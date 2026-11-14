import FaultDiamondHistories

/-!
Correcting all histories below an order bounds the operational diamond
distance by the same fault-tail probability.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix Asymptotics Filter
open CriticalDepth.FaultCPTPRepresentation CriticalDepth.FaultCPTPOptimality
open CriticalDepth.EncodedFaultRecovery CriticalDepth.IndependentFaultHistories
open scoped BigOperators ComplexOrder ENat Topology

noncomputable section

variable {Phys Log Loc : Type*} [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

theorem halfDiamond_history_le_tail (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (m : ℕ) (R : RecoveryChannel Phys Log)
    (hR : ∀ x, (faults x).card < m → recoverBranch R.val (A x) = LinearMap.id) :
    halfDiamondByEffects (recoveredHistoryChannel μ A p R) ≤
      ∑ x ∈ Finset.univ.filter (fun x : History Label => m ≤ (faults x).card), mass μ p x := by
  classical
  let bad := Finset.univ.filter (fun x : History Label => m ≤ (faults x).card)
  have hb : 0 ≤ ∑ x ∈ bad, mass μ p x :=
    Finset.sum_nonneg fun x _ => mass_nonneg μ hp hp₁ x
  apply real_sSup_le_of_nonneg
  · rintro _ ⟨n, X, E, hX, hE, rfl⟩
    have hsum : (∑ x : History Label, (mass μ p x : ℂ)) = 1 := by
      exact_mod_cast sum_mass μ p
    have he :
        amplify (recoveredHistoryChannel μ A p R) X - X =
          ∑ x : History Label, (mass μ p x : ℂ) • (amplify (recoverBranch R.val (A x)) X - X) := by
      unfold recoveredHistoryChannel
      rw [amplify_sum]
      simp_rw [amplify_smul, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    have hclass (x : History Label) : x ∉ bad → amplify (recoverBranch R.val (A x)) X = X := by
      intro hx
      have hlt : (faults x).card < m := Nat.lt_of_not_ge (fun h =>
        hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      rw [hR x hlt, amplify_id]
    have he' :
        amplify (recoveredHistoryChannel μ A p R) X - X =
          ∑ x ∈ bad, (mass μ p x : ℂ) • (amplify (recoverBranch R.val (A x)) X - X) := by
      rw [he]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      rw [hclass x hx, sub_self, smul_zero]
    have hval (s : Finset (History Label)) (f : History Label → Matrix (Fin n × Log) (Fin n × Log) ℂ) :
        effectValue E (∑ x ∈ s, f x) = ∑ x ∈ s, effectValue E (f x) := by
      induction s using Finset.induction_on with
      | empty => simp [effectValue]
      | @insert x s hx ih => rw [Finset.sum_insert hx, effectValue_add, ih, Finset.sum_insert hx]
    rw [he', hval]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro x _
    rw [effectValue_smul, abs_mul, abs_of_nonneg (mass_nonneg μ hp hp₁ x)]
    have hx := recoverBranch_isCPTP (A x) (hA x) R
    exact mul_le_of_le_one_right (mass_nonneg μ hp hp₁ x)
      (effectValue_difference_abs_le_one hE (amplify_preserves_density _ hx.1 hx.2 n hX) hX)
  · exact hb

theorem recoverBranch_eq_id_of_zero_loss (A : Matrix Phys Log ℂ)
    (hA : A.conjTranspose * A = 1) (R : TerminalRecovery Phys Log)
    (hLoss : branchLoss A R = 0) :
    recoverBranch (fromKraus R).val A = LinearMap.id := by
  choose c hc using (branchLoss_eq_zero_iff A hA R).mp hLoss
  have hnorm : (∑ j : Fin R.count, Complex.normSq (c j)) = 1 := by
    have hComp := composed_complete A hA R
    have h := congrArg (fun M : Matrix Log Log ℂ => M (Classical.choice inferInstance)
      (Classical.choice inferInstance)) hComp
    simp only [Matrix.sum_apply, hc, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    have ht := congrArg Complex.re h
    have hNorm (z : ℂ) : (z * star z).re = Complex.normSq z := by
      rw [mul_comm]
      change ((starRingEnd ℂ) z * z).re = _
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    simpa only [Complex.re_sum, hNorm, Complex.one_re] using ht
  rw [show (fromKraus R).val = krausMap R.kraus from rfl, recoverBranch_kraus]
  ext X i j
  change krausMap (fun k => R.kraus k * A) X i j = X i j
  rw [krausMap_apply, Matrix.sum_apply]
  have hTerm (k : Fin R.count) :
      (R.kraus k * A * X * (R.kraus k * A).conjTranspose) i j =
        (Complex.normSq (c k) : ℂ) * X i j := by
    rw [hc k, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, Matrix.smul_apply, smul_eq_mul]
    change ((starRingEnd ℂ) (c k) * c k) * X i j = _
    rw [← Complex.normSq_eq_conj_mul_self]
  simp_rw [hTerm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hnorm, Complex.ofReal_one, one_mul]

theorem guaranteed_historyDiamond_exponent (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (m : ℕ) (hscalar : ∀ x y, (faults x).card < m → (faults y).card < m →
      ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    (m : ℕ∞) ≤ FaultExponent.exponent (optimalHistoryDiamond μ A) := by
  classical
  let Good := {x : History Label // (faults x).card < m}
  let B (x : Good) := A x.val
  obtain ⟨R, hR⟩ := (common_zero_loss_iff B (fun x => hA x.val)).mpr
    (fun x y => hscalar x.val y.val x.property y.property)
  apply FaultExponent.exponent_ge
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨((Fintype.card Loc).choose m : ℝ), ?_⟩
  have hp₁ : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, by norm_num, subset_rfl⟩
  filter_upwards [hp₁] with p hp
  have hinf := optimalInfidelity_le_optimalHistoryDiamond μ A hA p hp.1.le hp.2.le
  have hnon := FaultExponent.optimalLoss_nonneg μ (fun x R => branchLoss (A x) R)
    (fun x R => (branchLoss_mem_Icc (A x) (hA x) R).1) hp.1.le hp.2.le
  have hn : 0 ≤ optimalHistoryDiamond μ A p := hnon.trans hinf
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hp.1.le _)]
  have hdom : BddBelow (Set.range fun T : RecoveryChannel Phys Log =>
      halfDiamondByEffects (recoveredHistoryChannel μ A p T)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact Real.sSup_nonneg (by rintro _ ⟨_, _, _, _, _, rfl⟩; exact abs_nonneg _)
  apply (csInf_le hdom (Set.mem_range_self (fromKraus R))).trans
  exact (halfDiamond_history_le_tail μ A hA p hp.1.le hp.2.le m (fromKraus R)
    (fun x hx => recoverBranch_eq_id_of_zero_loss (A x) (hA x) R (hR ⟨x, hx⟩))).trans
    (tail μ hp.1.le hp.2.le m)

#print axioms guaranteed_historyDiamond_exponent

end

end CriticalDepth.FaultChannelEffects