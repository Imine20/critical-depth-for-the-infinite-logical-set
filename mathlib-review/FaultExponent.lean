import FaultDepthArithmetic
import FaultHistoryLoss
import IndependentFaultHistories
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Order.LeftRightNhds

/-!
Asymptotic order and optimal terminal recovery for a finite fault
experiment. All recovery comparisons are uniform in the noise parameter.
-/

namespace CriticalDepth.FaultExponent

open Filter Set Asymptotics
open scoped BigOperators Topology ENat
open CriticalDepth.FaultProbability CriticalDepth.IndependentFaultHistories
open CriticalDepth.Manuscript20261114

noncomputable section

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
variable {Recovery : Type*} [Nonempty Recovery]

/-- Every candidate applies one recovery to all histories. -/
def lossAt (μ : Law Label) (loss : History Label → Recovery → ℝ)
    (p : ℝ) (r : Recovery) : ℝ :=
  expectedHistoryLoss Finset.univ (mass μ p) (fun x => loss x r)

def optimalLoss (μ : Law Label) (loss : History Label → Recovery → ℝ) (p : ℝ) : ℝ :=
  sInf (Set.range (lossAt μ loss p))

/-- The supremum of the integer orders with a right-hand big-O bound. -/
def exponent (ε : ℝ → ℝ) : ℕ∞ :=
  sSup {k : ℕ∞ | ∃ m : ℕ, k = (m : ℕ∞) ∧
    ε =O[𝓝[>] 0] fun p => p ^ m}

theorem exponent_ge {ε : ℝ → ℝ} (m : ℕ)
    (h : ε =O[𝓝[>] 0] fun p => p ^ m) : (m : ℕ∞) ≤ exponent ε :=
  le_sSup ⟨m, rfl, h⟩

theorem exponent_le_of_powerLower {ε : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (m : ℕ)
    (h : ∀ᶠ p in 𝓝[>] (0 : ℝ), c * p ^ m ≤ ε p) :
    exponent ε ≤ (m : ℕ∞) := by
  apply sSup_le
  rintro _ ⟨k, rfl, hk⟩
  by_contra! hkm
  have hmk : m < k := by exact_mod_cast hkm
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hk
  let good := {p : ℝ | c * p ^ m ≤ ε p ∧ ‖ε p‖ ≤ C * ‖p ^ k‖}
  have hgood : good ∈ 𝓝[>] (0 : ℝ) := h.and hC
  obtain ⟨δ, hδ, hδgood⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  change 0 < δ at hδ
  let p := min (δ / 2) (min (1 / 2) (c / (2 * (|C| + 1))))
  have habs : 0 ≤ |C| := abs_nonneg C
  have hp : 0 < p := lt_min (by linarith) (lt_min (by norm_num) (div_pos hc (by positivity)))
  have hpδ : p < δ := (min_le_left _ _).trans_lt (by linarith)
  have hp₁ : p ≤ 1 := (min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hpC : p ≤ c / (2 * (|C| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : (|C| + 1) * p < c := by
    have ht := (le_div_iff₀ (show 0 < 2 * (|C| + 1) by positivity)).mp hpC
    nlinarith
  obtain ⟨hl, hu⟩ := hδgood ⟨hp, hpδ⟩
  have hε : 0 ≤ ε p := (mul_nonneg hc.le (pow_nonneg hp.le _)).trans hl
  rw [Real.norm_eq_abs, abs_of_nonneg hε, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hp.le _)] at hu
  have hpow : p ^ k ≤ p ^ (m + 1) := pow_le_pow_of_le_one hp.le hp₁ hmk
  have hupper : C * p ^ k ≤ (|C| + 1) * p ^ (m + 1) :=
    mul_le_mul ((le_abs_self C).trans (by linarith)) hpow (pow_nonneg hp.le _) (by positivity)
  rw [pow_succ] at hupper
  have hstrict : (|C| + 1) * p * p ^ m < c * p ^ m :=
    mul_lt_mul_of_pos_right hsmall (pow_pos hp _)
  exact (not_lt_of_ge (hl.trans (hu.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hupper)))) hstrict

theorem optimalLoss_nonneg (μ : Law Label) (loss : History Label → Recovery → ℝ)
    (hnonneg : ∀ x r, 0 ≤ loss x r) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ optimalLoss μ loss p := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨r, rfl⟩
  exact Finset.sum_nonneg fun x _ => mul_nonneg (mass_nonneg μ hp hp₁ x) (hnonneg x r)

theorem guaranteed_exponent (μ : Law Label) (loss : History Label → Recovery → ℝ)
    (m : ℕ) (hrange : ∀ x r, loss x r ∈ Icc 0 1)
    (r : Recovery) (hcorrected : ∀ x, (faults x).card < m → loss x r = 0) :
    (m : ℕ∞) ≤ exponent (optimalLoss μ loss) := by
  apply exponent_ge
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨((Fintype.card Loc).choose m : ℝ), ?_⟩
  have hp₁ : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, by norm_num, subset_rfl⟩
  filter_upwards [hp₁] with p hp
  have hn := optimalLoss_nonneg μ loss (fun x r => (hrange x r).1) hp.1.le hp.2.le
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hp.1.le _)]
  have hb : BddBelow (Set.range (lossAt μ loss p)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r', rfl⟩
    exact Finset.sum_nonneg fun x _ => mul_nonneg (mass_nonneg μ hp.1.le hp.2.le x) (hrange x r').1
  apply (csInf_le hb (Set.mem_range_self r)).trans
  have hloss := expectedHistoryLoss_le_badMass
    (all := Finset.univ) (good := Finset.univ.filter fun x : History Label => (faults x).card < m)
    (mass μ p) (fun x => loss x r)
    (fun x _ => mass_nonneg μ hp.1.le hp.2.le x) (fun x _ => (hrange x r).2)
    (fun x hx => hcorrected x (Finset.mem_filter.mp hx).2)
  have htail : (Finset.univ : Finset (History Label)) \
      (Finset.univ.filter fun x : History Label => (faults x).card < m) =
      Finset.univ.filter fun x : History Label => m ≤ (faults x).card := by
    ext x
    simp [not_lt]
  exact (show lossAt μ loss p r ≤ _ from htail ▸ hloss).trans (tail μ hp.1.le hp.2.le m)

theorem ambiguous_exponent (μ : Law Label) (loss : History Label → Recovery → ℝ)
    (hnonneg : ∀ x r, 0 ≤ loss x r) (x y : History Label) (hxy : x ≠ y)
    (hambiguity : ∀ r, 1 ≤ loss x r + loss y r) :
    exponent (optimalLoss μ loss) ≤ ((max (faults x).card (faults y).card : ℕ) : ℕ∞) := by
  classical
  let w (z : History Label) := conditionalWeight μ z
  let k (z : History Label) := (faults z).card
  let clean (z : History Label) := Fintype.card Loc - k z
  let c := min (w x * (1 / 2 : ℝ) ^ clean x) (w y * (1 / 2 : ℝ) ^ clean y)
  have hc : 0 < c := lt_min
    (mul_pos (conditionalWeight_pos μ x) (pow_pos (by norm_num) _))
    (mul_pos (conditionalWeight_pos μ y) (pow_pos (by norm_num) _))
  apply exponent_le_of_powerLower hc
  have hhalf : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_, by norm_num, subset_rfl⟩
  filter_upwards [hhalf] with p hp
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨r, rfl⟩
  have hpair := (twoHistoriesPowerLower p (w x) (w y) (loss x r) (loss y r)
    (k x) (k y) (clean x) (clean y) hp.1.le hp.2.le
    (conditionalWeight_pos μ x) (conditionalWeight_pos μ y)
    (hnonneg x r) (hnonneg y r) (hambiguity r)).2
  change c * p ^ max (faults x).card (faults y).card ≤
    historyMass p (conditionalWeight μ x) (faults x).card (Fintype.card Loc - (faults x).card) * loss x r +
      historyMass p (conditionalWeight μ y) (faults y).card (Fintype.card Loc - (faults y).card) * loss y r at hpair
  rw [← mass_eq_historyMass μ p x, ← mass_eq_historyMass μ p y] at hpair
  apply hpair.trans
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun z => mass μ p z * loss z r) (Finset.subset_univ ({x, y} : Finset (History Label)))
    (fun z _ _ => mul_nonneg (mass_nonneg μ hp.1.le (by linarith [hp.2]) z) (hnonneg z r))
  simpa [Finset.sum_pair hxy, lossAt, expectedHistoryLoss] using hsum

/-- Infimum over all circuits, each with its own terminal recovery model. -/
def worstCaseExponent {Circuit : Type*} (ε : Circuit → ℝ → ℝ) : ℕ∞ :=
  ⨅ c, exponent (ε c)

theorem worstCaseExponent_bounds {Circuit : Type*} (ε : Circuit → ℝ → ℝ) (q d h : ℕ)
    (hfloor : ∀ c, (FaultDepthArithmetic.lowerEnvelope q d h : ℕ∞) ≤ exponent (ε c))
    (hceiling : ∃ c, exponent (ε c) ≤ (FaultDepthArithmetic.upperEnvelope q d h : ℕ∞)) :
    (FaultDepthArithmetic.lowerEnvelope q d h : ℕ∞) ≤ worstCaseExponent ε ∧
      worstCaseExponent ε ≤ (FaultDepthArithmetic.upperEnvelope q d h : ℕ∞) := by
  obtain ⟨c, hc⟩ := hceiling
  exact ⟨le_iInf hfloor, (iInf_le _ c).trans hc⟩

#print axioms exponent_le_of_powerLower
#print axioms guaranteed_exponent
#print axioms ambiguous_exponent
#print axioms worstCaseExponent_bounds

end
end CriticalDepth.FaultExponent
