import CriticalDepth.MainResults

/-!
# Positive-depth critical onset for the current manuscript

The current manuscript minimizes over positive depth budgets. The stronger
nonnegative-budget results remain available in MainResults. Finiteness at
budget zero makes the two critical-depth definitions equal, including when
neither definition has a finite value.
-/

noncomputable section

namespace CriticalDepth.Manuscript

variable {n ℓ g d k q : ℕ} {dim : Fin n → ℕ}

/-- The current manuscript's minimum over integer depth budgets h ≥ 1. -/
def hInfinityPositiveAtMost (C : Code n dim ℓ g) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, 1 ≤ h ∧ r = (h : ℕ∞) ∧
    (arbitraryLogicalImageAtMost C q h).Infinite}

/-- Excluding budget zero changes nothing when its logical image is finite. -/
theorem hInfinityPositiveAtMost_eq_hInfinityAtMost (C : Code n dim ℓ g) (q : ℕ)
    (hzero : (arbitraryLogicalImageAtMost C q 0).Finite) :
    hInfinityPositiveAtMost C q = hInfinityAtMost C q := by
  unfold hInfinityPositiveAtMost hInfinityAtMost
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨h, _hpositive, hr, hinfinite⟩
    exact ⟨h, hr, hinfinite⟩
  · rintro ⟨h, hr, hinfinite⟩
    have hpositive : 1 ≤ h := by
      by_contra hn
      have hz : h = 0 := by omega
      subst h
      exact hinfinite hzero
    exact ⟨h, hpositive, hr, hinfinite⟩

/-- The current Theorem 1 restricts attention to h ≥ 1 and q ≥ 2. -/
def theoremOnePositive : Prop :=
  ∀ (n ℓ g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ ℓ → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim ℓ g, DetectsBelow C d → ∀ q h : ℕ,
      2 ≤ q → 1 ≤ h → h < Arithmetic.criticalDepth q d →
      (arbitraryLogicalImageAtMost C q h).Finite ∧
        ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹'
          arbitraryLogicalImageAtMost C q h)

/-- A direct restriction of the stronger closed common-budget theorem. -/
theorem theoremOnePositive_proved : theoremOnePositive := by
  intro n ℓ g d dim hn hℓ hg hd C hdetect q h hq _hpositive hbelow
  exact theoremOneAtMost_proved n ℓ g d dim hn hℓ hg hd C hdetect q h
    (Or.inl ⟨hq, hbelow⟩)

private theorem positiveDepth_sites_positive (C : Code n dim ℓ g) (hd : 2 ≤ d)
    (hdistance : HasActualDistance C d) : 1 ≤ n := by
  obtain ⟨S, hS, _O, _hO, _hnongauge⟩ := hdistance.2
  have hsites : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

private theorem positiveDepth_two_le_two_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      rw [pow_succ]
      omega

private theorem positiveDepth_criticalDepth_positive (q d : ℕ)
    (hq : 2 ≤ q) (hd : 2 ≤ d) : 0 < Arithmetic.criticalDepth q d := by
  have hm : 0 < Nat.clog q d := Arithmetic.clog_pos_of_two_le q d hq hd
  unfold Arithmetic.criticalDepth
  omega

/-- Current Theorem 2 with its positive-depth definition of h∞. -/
def theoremTwoPositive : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinityPositiveAtMost C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
          HasContinuousLogicalSubgroupAtMost C q (Arithmetic.criticalDepth q d)

/-- The updated critical-depth conclusion follows from the closed main results. -/
theorem theoremTwoPositive_proved : theoremTwoPositive := by
  intro n k d q hk hd hq C hstabilizer hdistance
  have hzero : (arbitraryLogicalImageAtMost C q 0).Finite :=
    (theoremOneAtMost_proved n (2 ^ k) 1 d (fun _ => 2)
      (positiveDepth_sites_positive C hd hdistance) (positiveDepth_two_le_two_pow k hk)
      (by decide) hd C hdistance.1 q 0
      (Or.inl ⟨hq, positiveDepth_criticalDepth_positive q d hq hd⟩)).1
  obtain ⟨hcritical, hcontinuous⟩ :=
    theoremTwoAtMost_proved n k d q hk hd hq C hstabilizer hdistance
  exact ⟨(hInfinityPositiveAtMost_eq_hInfinityAtMost C q hzero).trans hcritical,
    hcontinuous⟩

end CriticalDepth.Manuscript
