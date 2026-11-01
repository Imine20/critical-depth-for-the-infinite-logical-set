import CriticalDepth.CircuitNormalization
import CriticalDepth.TheoremTwoReduction
import CriticalDepth.ProjectiveTopology
import Mathlib.Data.Set.Finite.Lattice

/-!
# The original common total-depth budget

The manuscript counts all circuits of depth at most h. The set below is the
finite union of the arbitrary-gate-list images at depths 0 through h. No
monotonicity of exact-depth images, identity-layer padding, or generated-group
closure is assumed.
-/

noncomputable section

namespace CriticalDepth.Manuscript

variable {n ℓ g d k q h : ℕ} {dim : Fin n → ℕ}

def arbitraryLogicalImageAtMost (C : Code n dim ℓ g) (q h : ℕ) :
    Set (ProjectiveOperator (Fin ℓ)) :=
  {a | ∃ r : ℕ, r ≤ h ∧ a ∈ arbitraryLogicalImage C q r}

theorem arbitraryLogicalImageAtMost_eq_iUnion (C : Code n dim ℓ g) (q h : ℕ) :
    arbitraryLogicalImageAtMost C q h =
      ⋃ r : Fin (h + 1), arbitraryLogicalImage C q r.val := by
  ext a
  constructor
  · rintro ⟨r, hr, ha⟩
    exact Set.mem_iUnion.mpr ⟨⟨r, Nat.lt_succ_of_le hr⟩, ha⟩
  · intro ha
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp ha
    exact ⟨r.val, Nat.le_of_lt_succ r.isLt, hr⟩

theorem arbitraryLogicalImage_subset_atMost (C : Code n dim ℓ g)
    (q r h : ℕ) (hr : r ≤ h) :
    arbitraryLogicalImage C q r ⊆ arbitraryLogicalImageAtMost C q h := by
  intro a ha
  exact ⟨r, hr, ha⟩

theorem logicalImage_subset_atMost (C : Code n dim ℓ g) (q r h : ℕ) (hr : r ≤ h) :
    logicalImage C q r ⊆ arbitraryLogicalImageAtMost C q h := by
  intro a ha
  exact ⟨r, hr, logicalImage_subset_arbitraryLogicalImage C ha⟩

theorem arbitraryLogicalImageAtMost_mono (C : Code n dim ℓ g) (q : ℕ)
    {h h' : ℕ} (hh : h ≤ h') :
    arbitraryLogicalImageAtMost C q h ⊆ arbitraryLogicalImageAtMost C q h' := by
  rintro a ⟨r, hr, ha⟩
  exact ⟨r, hr.trans hh, ha⟩

theorem arbitraryLogicalImageAtMost_finite_of_exact (C : Code n dim ℓ g) (q h : ℕ)
    (hexact : ∀ r : ℕ, r ≤ h → (arbitraryLogicalImage C q r).Finite) :
    (arbitraryLogicalImageAtMost C q h).Finite := by
  rw [arbitraryLogicalImageAtMost_eq_iUnion]
  apply Set.finite_iUnion
  intro r
  exact hexact r.val (Nat.le_of_lt_succ r.isLt)

/-- The finite common-budget image follows from actual exact-depth finiteness. -/
theorem arbitraryLogicalImageAtMost_finite_of_theoremOne (hT1 : theoremOne)
    (C : Code n dim ℓ g) (hn : 1 ≤ n) (hℓ : 2 ≤ ℓ) (hg : 1 ≤ g) (hd : 2 ≤ d)
    (hdetect : DetectsBelow C d) (q h : ℕ)
    (hbudget : (2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) :
    (arbitraryLogicalImageAtMost C q h).Finite := by
  apply arbitraryLogicalImageAtMost_finite_of_exact C q h
  intro r hr
  have hrbudget : (2 ≤ q ∧ r < Arithmetic.criticalDepth q d) ∨ q = 1 := by
    rcases hbudget with ⟨hq, hh⟩ | hq
    · exact Or.inl ⟨hq, hr.trans_lt hh⟩
    · exact Or.inr hq
  have hfinite := hT1 n ℓ g d dim hn hℓ hg hd C hdetect q r hrbudget
  exact arbitraryLogicalImage_finite_of_logicalImage_finite C hℓ hg hfinite

theorem arbitraryLogicalImageAtMost_not_dense (C : Code n dim ℓ g) (q h : ℕ)
    (hℓ : 2 ≤ ℓ) (hfinite : (arbitraryLogicalImageAtMost C q h).Finite) :
    ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' arbitraryLogicalImageAtMost C q h) :=
  finite_projectiveImage_not_dense_in_projectiveUnitary ℓ hℓ _ hfinite

/-- Source Theorem 1 with its original total-depth budget and non-density conclusion. -/
def theoremOneAtMost : Prop :=
  ∀ (n ℓ g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ ℓ → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim ℓ g, DetectsBelow C d → ∀ q h : ℕ,
      ((2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) →
      (arbitraryLogicalImageAtMost C q h).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' arbitraryLogicalImageAtMost C q h)

theorem theoremOneAtMost_of_theoremOne (hT1 : theoremOne) : theoremOneAtMost := by
  intro n ℓ g d dim hn hℓ hg hd C hdetect q h hbudget
  have hfinite := arbitraryLogicalImageAtMost_finite_of_theoremOne hT1 C
    hn hℓ hg hd hdetect q h hbudget
  exact ⟨hfinite, arbitraryLogicalImageAtMost_not_dense C q h hℓ hfinite⟩

def hInfinityAtMost (C : Code n dim ℓ g) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, r = (h : ℕ∞) ∧ (arbitraryLogicalImageAtMost C q h).Infinite}

def HasContinuousLogicalSubgroupAtMost (C : Code n (fun _ => 2) ℓ 1) (q h : ℕ) : Prop :=
  ∃ W : ℝ → Operator (Fin ℓ), Continuous W ∧
    (∀ t, IsUnitary (W t)) ∧ W 0 = 1 ∧
    (∀ s t, W (s + t) = W s * W t) ∧
    (∃ t, ¬ ProjectivelyEquivalent (W t) 1) ∧
    (∀ t, projectiveClass (W t) ∈ arbitraryLogicalImageAtMost C q h)

theorem HasContinuousLogicalSubgroup.atMost (C : Code n (fun _ => 2) ℓ 1)
    (q h : ℕ) (hexact : HasContinuousLogicalSubgroup C q h) :
    HasContinuousLogicalSubgroupAtMost C q h := by
  obtain ⟨W, hcont, hunit, hzero, hadd, hnontriv, hmem⟩ := hexact
  refine ⟨W, hcont, hunit, hzero, hadd, hnontriv, ?_⟩
  intro t
  exact logicalImage_subset_atMost C q h h (le_refl _) (hmem t)

theorem hInfinityAtMost_eq_of_finite_below_and_infinite_at
    (C : Code n dim ℓ g) (q H : ℕ)
    (hbelow : ∀ h : ℕ, h < H → (arbitraryLogicalImageAtMost C q h).Finite)
    (hat : (arbitraryLogicalImageAtMost C q H).Infinite) :
    hInfinityAtMost C q = (H : ℕ∞) := by
  unfold hInfinityAtMost
  apply le_antisymm
  · exact sInf_le ⟨H, rfl, hat⟩
  · apply le_sInf
    rintro r ⟨h, rfl, hinfinite⟩
    have hnat : H ≤ h := by
      by_contra hn
      have hlt : h < H := by omega
      exact hinfinite (hbelow h hlt)
    exact_mod_cast hnat

private theorem budget_two_le_two_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      rw [pow_succ]
      omega

private theorem budget_sites_positive (C : Code n dim ℓ g) (hd : 2 ≤ d)
    (hdistance : HasActualDistance C d) : 1 ≤ n := by
  obtain ⟨S, hS, _O, _hO, _hnon⟩ := hdistance.2
  have hsites : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- Source Theorem 2 with the original at-most-depth definition of the critical depth. -/
def theoremTwoAtMost : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinityAtMost C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
        HasContinuousLogicalSubgroupAtMost C q (Arithmetic.criticalDepth q d)

/-- Explicit conditional reduction; root must supply an actual Theorem 1 proof. -/
theorem theoremTwoAtMost_of_theoremOne (hT1 : theoremOne) : theoremTwoAtMost := by
  intro n k d q hk hd hq C hstabilizer hdistance
  obtain ⟨hinfinite, hcontinuous⟩ :=
    stabilizer_critical_logical_image C hk hd hq hstabilizer hdistance
  have hatmost : (arbitraryLogicalImageAtMost C q (Arithmetic.criticalDepth q d)).Infinite :=
    hinfinite.mono (logicalImage_subset_atMost C q (Arithmetic.criticalDepth q d)
      (Arithmetic.criticalDepth q d) (le_refl _))
  refine ⟨?_, HasContinuousLogicalSubgroup.atMost C q _ hcontinuous⟩
  apply hInfinityAtMost_eq_of_finite_below_and_infinite_at C q
    (Arithmetic.criticalDepth q d) ?_ hatmost
  intro h hh
  exact arbitraryLogicalImageAtMost_finite_of_theoremOne hT1 C
    (budget_sites_positive C hd hdistance) (budget_two_le_two_pow k hk) (by decide) hd
    hdistance.1 q h (Or.inl ⟨hq, hh⟩)

end CriticalDepth.Manuscript
