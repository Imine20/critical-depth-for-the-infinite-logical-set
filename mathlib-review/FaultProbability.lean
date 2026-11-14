import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite fault-history probability bounds

The estimates here apply to the probabilities of fault histories. The
conditional infidelity premise of the two-history lemma comes from a separate
argument about recovered Choi states.
-/

namespace CriticalDepth.FaultProbability

noncomputable section

open scoped BigOperators

def historyMass (p weight : ℝ) (faults clean : ℕ) : ℝ :=
  weight * p ^ faults * (1 - p) ^ clean

/-- A specified history has positive lower and upper constants at its own
fault order. The weight is the product of the conditional Pauli probabilities. -/
theorem historyMassBounds (p weight : ℝ) (faults clean : ℕ)
    (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2) (hw : 0 ≤ weight) :
    weight * (1 / 2 : ℝ) ^ clean * p ^ faults ≤ historyMass p weight faults clean ∧
      historyMass p weight faults clean ≤ weight * p ^ faults := by
  have hmid : (1 / 2 : ℝ) ≤ 1 - p := by linarith
  have hclean : 0 ≤ 1 - p := by linarith
  have hbase : 0 ≤ weight * p ^ faults := mul_nonneg hw (pow_nonneg hp _)
  unfold historyMass
  constructor
  · rw [mul_right_comm weight]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hmid clean) hbase
  · have hpow : (1 - p) ^ clean ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hclean (show 1 - p ≤ 1 by linarith) clean
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hbase

theorem minMass_le_weightedInfidelity (a b e₀ e₁ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁)
    (hsum : 1 ≤ e₀ + e₁) :
    min a b ≤ a * e₀ + b * e₁ := by
  have hm : 0 ≤ min a b := le_min ha hb
  calc
    min a b = min a b * 1 := (mul_one _).symm
    _ ≤ min a b * (e₀ + e₁) := mul_le_mul_of_nonneg_left hsum hm
    _ = min a b * e₀ + min a b * e₁ := mul_add _ _ _
    _ ≤ a * e₀ + b * e₁ := add_le_add
      (mul_le_mul_of_nonneg_right (min_le_left _ _) he₀)
      (mul_le_mul_of_nonneg_right (min_le_right _ _) he₁)

/-- The bound holds for every pair of conditional infidelities satisfying the
orthogonality estimate, even if they depend on the noise parameter. -/
theorem twoHistoriesPowerLower (p w₀ w₁ e₀ e₁ : ℝ) (k₀ k₁ c₀ c₁ : ℕ)
    (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2) (hw₀ : 0 < w₀) (hw₁ : 0 < w₁)
    (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁) (hsum : 1 ≤ e₀ + e₁) :
    0 < min (w₀ * (1 / 2 : ℝ) ^ c₀) (w₁ * (1 / 2 : ℝ) ^ c₁) ∧
      min (w₀ * (1 / 2 : ℝ) ^ c₀) (w₁ * (1 / 2 : ℝ) ^ c₁) * p ^ max k₀ k₁ ≤
        historyMass p w₀ k₀ c₀ * e₀ + historyMass p w₁ k₁ c₁ * e₁ := by
  have ha : 0 < w₀ * (1 / 2 : ℝ) ^ c₀ := mul_pos hw₀ (pow_pos (by norm_num) _)
  have hb : 0 < w₁ * (1 / 2 : ℝ) ^ c₁ := mul_pos hw₁ (pow_pos (by norm_num) _)
  have hp1 : p ≤ 1 := by linarith
  have hm : 0 < min (w₀ * (1 / 2 : ℝ) ^ c₀) (w₁ * (1 / 2 : ℝ) ^ c₁) :=
    lt_min_iff.mpr ⟨ha, hb⟩
  refine ⟨hm, ?_⟩
  have h₀ := (historyMassBounds p w₀ k₀ c₀ hp hpHalf hw₀.le).1
  have h₁ := (historyMassBounds p w₁ k₁ c₁ hp hpHalf hw₁.le).1
  have h₀' : 0 ≤ historyMass p w₀ k₀ c₀ :=
    (mul_nonneg ha.le (pow_nonneg hp _)).trans h₀
  have h₁' : 0 ≤ historyMass p w₁ k₁ c₁ :=
    (mul_nonneg hb.le (pow_nonneg hp _)).trans h₁
  apply le_trans ?_ (minMass_le_weightedInfidelity _ _ e₀ e₁ h₀' h₁' he₀ he₁ hsum)
  apply le_min
  · exact (mul_le_mul (min_le_left _ _) (pow_le_pow_of_le_one hp hp1 (le_max_left _ _))
      (pow_nonneg hp _) ha.le).trans h₀
  · exact (mul_le_mul (min_le_right _ _) (pow_le_pow_of_le_one hp hp1 (le_max_right _ _))
      (pow_nonneg hp _) hb.le).trans h₁

/-- A finite union bound for the mass of histories with at least `m` faulty
locations. The local-stochastic hypothesis is on joint fault events. -/
theorem localStochasticTail {Hist Loc : Type*} [DecidableEq Loc]
    (histories : Finset Hist) (locations : Finset Loc)
    (faults : Hist → Finset Loc) (mass : Hist → ℝ) (m : ℕ) (p : ℝ)
    (hnonneg : ∀ i ∈ histories, 0 ≤ mass i)
    (hsub : ∀ i ∈ histories, faults i ⊆ locations)
    (hjoint : ∀ s ⊆ locations, ∑ i ∈ histories.filter (fun i => s ⊆ faults i), mass i ≤
      p ^ s.card) :
    ∑ i ∈ histories.filter (fun i => m ≤ (faults i).card), mass i ≤
      (locations.card.choose m : ℝ) * p ^ m := by
  classical
  have hpoint (i : Hist) (hi : i ∈ histories) :
      (if m ≤ (faults i).card then mass i else 0) ≤
        ∑ s ∈ locations.powersetCard m, if s ⊆ faults i then mass i else 0 := by
    split_ifs with hm
    · obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hm
      have hmem : s ∈ locations.powersetCard m :=
        Finset.mem_powersetCard.mpr ⟨hs.trans (hsub i hi), hcard⟩
      have hone := Finset.single_le_sum
        (f := fun s => if s ⊆ faults i then mass i else 0)
        (fun a _ => by
          by_cases ha : a ⊆ faults i
          · simpa only [if_pos ha] using hnonneg i hi
          · simp only [if_neg ha, le_refl]) hmem
      simpa only [if_pos hs] using hone
    · exact Finset.sum_nonneg (fun s _ => by
        by_cases hs : s ⊆ faults i
        · simpa only [if_pos hs] using hnonneg i hi
        · simp only [if_neg hs, le_refl])
  calc
    _ = ∑ i ∈ histories, if m ≤ (faults i).card then mass i else 0 :=
      Finset.sum_filter _ _
    _ ≤ ∑ i ∈ histories, ∑ s ∈ locations.powersetCard m,
        if s ⊆ faults i then mass i else 0 := Finset.sum_le_sum hpoint
    _ = ∑ s ∈ locations.powersetCard m, ∑ i ∈ histories,
        if s ⊆ faults i then mass i else 0 := Finset.sum_comm
    _ ≤ ∑ _s ∈ locations.powersetCard m, p ^ m := by
      apply Finset.sum_le_sum
      intro s hs
      rw [← Finset.sum_filter]
      obtain ⟨hsubset, hcard⟩ := Finset.mem_powersetCard.mp hs
      simpa only [hcard] using hjoint s hsubset
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]

example (p : ℝ) (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2) :
    (1 / 8 : ℝ) * p ^ 2 ≤ historyMass p 1 2 3 := by
  have h := (historyMassBounds p 1 2 3 hp hpHalf (by norm_num)).1
  norm_num at h
  exact h

example (p e₀ e₁ : ℝ) (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁) (hsum : 1 ≤ e₀ + e₁) :
    (1 / 8 : ℝ) * p ^ 3 ≤ historyMass p 1 2 3 * e₀ + historyMass p 1 3 2 * e₁ := by
  have h := (twoHistoriesPowerLower p 1 1 e₀ e₁ 2 3 3 2
    hp hpHalf (by norm_num) (by norm_num) he₀ he₁ hsum).2
  norm_num at h
  exact h

example {Hist : Type*} (histories : Finset Hist) (faults : Hist → Finset (Fin 3))
    (mass : Hist → ℝ) (p : ℝ) (hnonneg : ∀ i ∈ histories, 0 ≤ mass i)
    (hjoint : ∀ s : Finset (Fin 3),
      ∑ i ∈ histories.filter (fun i => s ⊆ faults i), mass i ≤ p ^ s.card) :
    ∑ i ∈ histories.filter (fun i => 2 ≤ (faults i).card), mass i ≤ 3 * p ^ 2 := by
  have h := localStochasticTail histories (Finset.univ : Finset (Fin 3)) faults mass 2 p
    hnonneg (fun i _ => Finset.subset_univ (faults i)) (fun s _ => hjoint s)
  norm_num at h
  exact h

#print axioms historyMassBounds
#print axioms minMass_le_weightedInfidelity
#print axioms twoHistoriesPowerLower
#print axioms localStochasticTail

end

end CriticalDepth.FaultProbability
