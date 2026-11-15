import FaultFirstBadOrderLower
import FaultFirstBadOrderUpper
import FaultHaarOptimality

/-! The first failure of joint exact recovery determines the error order. -/

namespace CriticalDepth.FaultFirstBadOrder

open Matrix Filter Asymptotics
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultChannelEffects
open CriticalDepth.FaultAverageInfidelity
open scoped Topology ENat

noncomputable section

variable {Phys Log Loc : Type*} [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

/-- All histories through order m meet the same Knill–Laflamme condition. -/
def correctableThrough (A : History Label → Matrix Phys Log ℂ) (m : ℕ) : Prop :=
  ∀ x y, (faults x).card ≤ m → (faults y).card ≤ m →
    ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)

theorem correctableThrough_iff_common_cptp_recovery
    (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) (m : ℕ) :
    correctableThrough A m ↔ ∃ R : RecoveryChannel Phys Log,
      ∀ x, (faults x).card ≤ m → recoverBranch R.val (A x) = LinearMap.id := by
  classical
  let Good := {x : History Label // (faults x).card ≤ m}
  let B (x : Good) := A x.val
  let bridge := common_cptp_recovery_iff_scalarCrossTerms B (fun x => hA x.val)
  constructor
  · intro h
    obtain ⟨R, hR⟩ := bridge.mpr (fun x y => h x.val y.val x.property y.property)
    exact ⟨R, fun x hx => hR ⟨x, hx⟩⟩
  · rintro ⟨R, hR⟩ x y hx hy
    exact bridge.mp ⟨R, fun a => hR a.val a.property⟩ ⟨x, hx⟩ ⟨y, hy⟩

theorem correctableThrough_zero (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    correctableThrough A 0 := by
  have hClean (x : History Label) (hx : (faults x).card ≤ 0) (i : Loc) : x i = none := by
    have he : faults x = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hx)
    by_contra hn
    have hi : i ∈ faults x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    simpa only [he, Finset.notMem_empty] using hi
  intro x y hx hy
  have he : x = y := funext fun i => (hClean x hx i).trans (hClean y hy i).symm
  subst y
  exact ⟨1, by simpa only [one_smul] using hA x⟩
/-- The order of the first failure is independent of the strictly positive noise weights. -/
def firstUncorrectableOrder (A : History Label → Matrix Phys Log ℂ) : ℕ∞ := by
  classical
  exact if h : ∃ m, ¬ correctableThrough A m then (Nat.find h : ℕ∞) else ⊤

private theorem eventually_small_noise : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
  mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, by norm_num, subset_rfl⟩

private theorem power_isBigO_of_eventual_lower {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (m : ℕ) (h : ∀ᶠ p in 𝓝[>] (0 : ℝ), c * p ^ m ≤ f p) :
    (fun p : ℝ => p ^ m) =O[𝓝[>] (0 : ℝ)] f := by
  apply isBigO_iff.mpr
  refine ⟨c⁻¹, ?_⟩
  filter_upwards [h, eventually_small_noise] with p hLower hp
  have hpPow : 0 ≤ p ^ m := pow_nonneg hp.1.le _
  have hf : 0 ≤ f p := (mul_nonneg hc.le hpPow).trans hLower
  simp only [Real.norm_eq_abs, abs_of_nonneg hpPow, abs_of_nonneg hf]
  have hMul := mul_le_mul_of_nonneg_left hLower (inv_nonneg.mpr hc.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hMul

/-- Once exact joint recovery fails at order m and works below it, every
optimized metric has a two-sided power bound for the same experiment. -/
theorem historyErrors_isTheta_of_first_failure
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) (m : ℕ)
    (hgood : ∀ j < m, correctableThrough A j)
    (hbad : ¬ correctableThrough A m) :
    (optimalInfidelity μ A =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
    (optimalAverageInfidelity μ A =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
    (optimalHistoryDiamond μ A =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) := by
  obtain ⟨c, hc, hLower⟩ :=
    optimalInfidelity_eventual_powerLower_of_bad_order μ A hA m hbad
  have hD := optimalHistoryDiamond_isBigO_of_scalarCrossTerms μ A hA m (by
    intro x y hx hy
    exact hgood (max (faults x).card (faults y).card) (max_lt hx hy) x y
      (le_max_left _ _) (le_max_right _ _))
  have hCompare : ∀ᶠ p in 𝓝[>] (0 : ℝ),
      optimalInfidelity μ A p ≤ optimalHistoryDiamond μ A p := by
    filter_upwards [eventually_small_noise] with p hp
    exact optimalInfidelity_le_optimalHistoryDiamond μ A hA p hp.1.le hp.2.le
  have hEnt : optimalInfidelity μ A =O[𝓝[>] (0 : ℝ)] fun p => p ^ m := by
    obtain ⟨C, hC⟩ := isBigO_iff.mp hD
    apply isBigO_iff.mpr
    refine ⟨C, ?_⟩
    filter_upwards [hC, hCompare, hLower, eventually_small_noise] with p hC hCompare hLower hp
    have hEnt_nonneg : 0 ≤ optimalInfidelity μ A p :=
      (mul_nonneg hc.le (pow_nonneg hp.1.le _)).trans hLower
    have hDiamond_nonneg := hEnt_nonneg.trans hCompare
    have hnorm : ‖optimalInfidelity μ A p‖ ≤ ‖optimalHistoryDiamond μ A p‖ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hEnt_nonneg, abs_of_nonneg hDiamond_nonneg]
        using hCompare
    exact hnorm.trans hC
  have hDL : ∀ᶠ p in 𝓝[>] (0 : ℝ), c * p ^ m ≤ optimalHistoryDiamond μ A p := by
    filter_upwards [hCompare, hLower] with p hCompare hLower
    exact hLower.trans hCompare
  let b := fidelityDimensionRatio Log
  have hb : 0 < b := fidelityDimensionRatio_pos Log
  have hAvg : optimalAverageInfidelity μ A = fun p => b * optimalInfidelity μ A p :=
    funext (optimalAverageInfidelity_eq_dim_ratio μ A hA)
  have hAL : ∀ᶠ p in 𝓝[>] (0 : ℝ), (b * c) * p ^ m ≤ optimalAverageInfidelity μ A p := by
    filter_upwards [hLower] with p hp
    rw [hAvg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hb.le
  refine ⟨⟨hEnt, power_isBigO_of_eventual_lower hc m hLower⟩, ⟨?_, ?_⟩,
    ⟨hD, power_isBigO_of_eventual_lower hc m hDL⟩⟩
  · rw [hAvg]
    exact hEnt.const_mul_left b
  · exact power_isBigO_of_eventual_lower (mul_pos hb hc) m hAL

/-- Complete dichotomy for one finite independent fault experiment. -/
theorem historyErrors_firstUncorrectableOrder
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    (firstUncorrectableOrder A = ⊤ ∧
      ∃ R : RecoveryChannel Phys Log,
        (∀ x, recoverBranch R.val (A x) = LinearMap.id) ∧
        ∀ p, 0 ≤ p → p ≤ 1 →
          optimalInfidelity μ A p = 0 ∧ optimalAverageInfidelity μ A p = 0 ∧
          optimalHistoryDiamond μ A p = 0) ∨
    (∃ m : ℕ, firstUncorrectableOrder A = (m : ℕ∞) ∧
      (∀ j < m, correctableThrough A j) ∧ ¬ correctableThrough A m ∧
      (optimalInfidelity μ A =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
      (optimalAverageInfidelity μ A =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
      (optimalHistoryDiamond μ A =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m)) := by
  classical
  by_cases hex : ∃ m, ¬ correctableThrough A m
  · right
    let m := Nat.find hex
    have hbad : ¬ correctableThrough A m := Nat.find_spec hex
    have hgood (j : ℕ) (hj : j < m) : correctableThrough A j := by
      by_contra hj'
      exact (not_lt_of_ge (Nat.find_min' hex hj')) hj
    exact ⟨m, by simp [firstUncorrectableOrder, hex, m], hgood, hbad,
      historyErrors_isTheta_of_first_failure μ A hA m hgood hbad⟩
  · left
    have hall (j : ℕ) : correctableThrough A j := by
      by_contra hj
      exact hex ⟨j, hj⟩
    obtain ⟨R, hR⟩ := exists_common_cptp_recovery_of_all_scalarCrossTerms A hA (by
      intro x y
      exact hall (max (faults x).card (faults y).card) x y (le_max_left _ _) (le_max_right _ _))
    refine ⟨by simp [firstUncorrectableOrder, hex], R, hR, ?_⟩
    intro p hp hp₁
    have hE := optimalInfidelity_eq_zero_of_common_cptp_recovery μ A hA p hp hp₁ R hR
    refine ⟨hE, ?_, optimalHistoryDiamond_eq_zero_of_common_cptp_recovery μ A hA p hp hp₁ R hR⟩
    rw [optimalAverageInfidelity_eq_dim_ratio μ A hA, hE, mul_zero]

theorem exponent_eq_of_powerTheta {ε : ℝ → ℝ} (m : ℕ)
    (h : ε =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) :
    FaultExponent.exponent ε = (m : ℕ∞) := by
  apply le_antisymm _ (FaultExponent.exponent_ge m h.1)
  have hPow : FaultExponent.exponent (fun p : ℝ => p ^ m) ≤ (m : ℕ∞) :=
    FaultExponent.exponent_le_of_powerLower (by norm_num : (0 : ℝ) < 1) m
      (Eventually.of_forall fun p => by simp)
  apply sSup_le
  rintro _ ⟨k, rfl, hk⟩
  exact (FaultExponent.exponent_ge k (h.2.trans hk)).trans hPow

private theorem exponent_eq_top_of_eventually_zero {ε : ℝ → ℝ}
    (h : ∀ᶠ p in 𝓝[>] (0 : ℝ), ε p = 0) : FaultExponent.exponent ε = ⊤ := by
  apply le_antisymm le_top
  by_contra! htop
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt htop)
  have hO : ε =O[𝓝[>] (0 : ℝ)] fun p => p ^ (k + 1) := by
    apply isBigO_iff.mpr
    refine ⟨0, ?_⟩
    filter_upwards [h] with p hp
    simp [hp]
  have hlt := FaultExponent.exponent_ge (k + 1) hO
  rw [← hk] at hlt
  exact (Nat.not_succ_le_self k) (by exact_mod_cast hlt)

theorem historyErrorExponents_eq_firstUncorrectableOrder
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    FaultExponent.exponent (optimalInfidelity μ A) = firstUncorrectableOrder A ∧
    FaultExponent.exponent (optimalAverageInfidelity μ A) = firstUncorrectableOrder A ∧
    FaultExponent.exponent (optimalHistoryDiamond μ A) = firstUncorrectableOrder A := by
  rcases historyErrors_firstUncorrectableOrder μ A hA with h | h
  · obtain ⟨hOrder, R, hR, hZero⟩ := h
    rw [hOrder]
    have hz : ∀ᶠ p in 𝓝[>] (0 : ℝ), optimalInfidelity μ A p = 0 ∧
        optimalAverageInfidelity μ A p = 0 ∧ optimalHistoryDiamond μ A p = 0 := by
      filter_upwards [eventually_small_noise] with p hp
      exact hZero p hp.1.le hp.2.le
    exact ⟨exponent_eq_top_of_eventually_zero (hz.mono fun _ h => h.1),
      exponent_eq_top_of_eventually_zero (hz.mono fun _ h => h.2.1),
      exponent_eq_top_of_eventually_zero (hz.mono fun _ h => h.2.2)⟩
  · obtain ⟨m, hm, _, _, he, ha, hd⟩ := h
    rw [hm]
    exact ⟨exponent_eq_of_powerTheta m he, exponent_eq_of_powerTheta m ha,
      exponent_eq_of_powerTheta m hd⟩

#print axioms correctableThrough_iff_common_cptp_recovery
#print axioms correctableThrough_zero
#print axioms historyErrors_isTheta_of_first_failure
#print axioms historyErrors_firstUncorrectableOrder
#print axioms exponent_eq_of_powerTheta
#print axioms historyErrorExponents_eq_firstUncorrectableOrder

end
end CriticalDepth.FaultFirstBadOrder