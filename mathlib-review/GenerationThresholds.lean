import CriticalDepthMathlib
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Dense and exact logical generation

The threshold definitions use the native projective unitary image. The
unconditional lower bound uses finite-word countability. The matching upper
bound is reduced to the identity-neighborhood step of the geometric argument.
-/

open scoped Topology

noncomputable section

namespace CriticalDepth.ReviewV2

open CriticalDepth.Manuscript

section GeneratedSubgroups

variable {G : Type*} [Group G]

/-- A countable alphabet and its inverses generate a countable group of finite words. -/
theorem subgroupClosure_ne_top_of_countable [Uncountable G] {S : Set G}
    (hS : S.Countable) : Subgroup.closure S ≠ ⊤ := by
  let : Countable S := hS
  let : Encodable S := Encodable.ofCountable S
  have hWords : Function.Surjective
      (FreeGroup.mk : List (S × Bool) → FreeGroup S) := by
    intro word
    exact Quot.inductionOn word (fun representative => ⟨representative, rfl⟩)
  let : Countable (FreeGroup S) := hWords.countable
  intro hTop
  rw [FreeGroup.closure_eq_range] at hTop
  exact not_countable (MonoidHom.range_eq_top.mp hTop).countable

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- An identity neighborhood in a dense subgroup suffices for equality with the full group. -/
theorem dense_subgroup_eq_top_of_one_nhds (H : Subgroup G)
    (hdense : H.topologicalClosure = ⊤) (hNhd : (H : Set G) ∈ 𝓝 1) : H = ⊤ := by
  have hopen : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hNhd
  have hclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  apply top_unique
  rw [← hdense]
  exact H.topologicalClosure_minimal le_rfl hclosed

/-- A closed proper subgroup containing the alphabet also contains the closure of its words. -/
theorem not_dense_subgroupClosure_of_subset_closed {S : Set G} {H : Subgroup G}
    (hS : S ⊆ H) (hclosed : IsClosed (H : Set G)) (hproper : H ≠ ⊤) :
    (Subgroup.closure S).topologicalClosure ≠ ⊤ := by
  intro hdense
  have hle := (Subgroup.closure S).topologicalClosure_minimal
    ((Subgroup.closure_le H).2 hS) hclosed
  rw [hdense] at hle
  exact hproper (top_unique hle)

end GeneratedSubgroups

/-- The projective unitary group has an uncountable family of distinct classes for K ≥ 2. -/
theorem nativePU_uncountable (K : ℕ) (hK : 2 ≤ K) : Uncountable (PU (Fin K)) := by
  have hParam : Function.Injective (fun x : ℝ => Circle.exp (Real.arctan x)) := by
    intro x y hxy
    apply Real.arctan_injective
    have hbound : Real.pi / 2 - -(Real.pi / 2) < 2 * Real.pi := by
      linarith [Real.pi_pos]
    exact Circle.exp_injOn_Icc hbound
      (Set.Ioo_subset_Icc_self (Real.arctan_mem_Ioo x))
      (Set.Ioo_subset_Icc_self (Real.arctan_mem_Ioo y)) hxy
  have hCircle := circleProjectiveHom_injective
    (signInvolution_selfAdjoint K) (signInvolution_sq K) (signInvolution_not_isScalar K hK)
  exact (hCircle.comp hParam).uncountable

/-- The first positive depth satisfying a property, with infinity for an empty set. -/
def positiveDepthInf (P : ℕ → Prop) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, 1 ≤ h ∧ r = (h : ℕ∞) ∧ P h}

theorem positiveDepthInf_le_nat_iff {P : ℕ → Prop}
    (hmono : ∀ ⦃i j⦄, i ≤ j → P i → P j) (h : ℕ) :
    positiveDepthInf P ≤ (h : ℕ∞) ↔ 1 ≤ h ∧ P h := by
  constructor
  · intro hle
    have hlt : positiveDepthInf P < ((h + 1 : ℕ) : ℕ∞) :=
      hle.trans_lt (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self h))
    obtain ⟨_, ⟨j, hj, rfl, hP⟩, hjlt⟩ := sInf_lt_iff.mp hlt
    have hjle : j ≤ h := Nat.lt_succ_iff.mp (ENat.natCast_lt_natCast.mp hjlt)
    exact ⟨hj.trans hjle, hmono hjle hP⟩
  · rintro ⟨hh, hP⟩
    exact sInf_le ⟨h, hh, rfl, hP⟩

theorem positiveDepthInf_antitone {P Q : ℕ → Prop} (hPQ : ∀ h, P h → Q h) :
    positiveDepthInf Q ≤ positiveDepthInf P := by
  apply le_sInf
  rintro _ ⟨h, hh, rfl, hP⟩
  exact sInf_le ⟨h, hh, rfl, hPQ h hP⟩

variable {n K g : ℕ} {dim : Fin n → ℕ}

/-- The subgroup of finite words in classes with native circuit depth at most h. -/
def generatedLogicalSubgroup
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) (q h : ℕ) :
    Subgroup (PU (Fin K)) :=
  Subgroup.closure (nativeLogicalImage V q h)

def nativeDenseDepth (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) (q : ℕ) : ℕ∞ :=
  positiveDepthInf (fun h => (generatedLogicalSubgroup V q h).topologicalClosure = ⊤)

def nativeExactDepth (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) (q : ℕ) : ℕ∞ :=
  positiveDepthInf (fun h => generatedLogicalSubgroup V q h = ⊤)

variable (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) (q : ℕ)

theorem nativeLogicalImage_mono_depth {i j : ℕ} (hij : i ≤ j) :
    nativeLogicalImage V q i ⊆ nativeLogicalImage V q j := by
  rintro x ⟨r, hr, c, hc, W, Z, hEval, hClass⟩
  exact ⟨r, hr.trans hij, c, hc, W, Z, hEval, hClass⟩

theorem generatedLogicalSubgroup_mono {i j : ℕ} (hij : i ≤ j) :
    generatedLogicalSubgroup V q i ≤ generatedLogicalSubgroup V q j :=
  Subgroup.closure_mono (nativeLogicalImage_mono_depth V q hij)

theorem nativeCriticalDepth_le_nat_iff (h : ℕ) :
    nativeCriticalDepth V q ≤ (h : ℕ∞) ↔ 1 ≤ h ∧ (nativeLogicalImage V q h).Infinite := by
  apply positiveDepthInf_le_nat_iff
  intro i j hij hi
  exact hi.mono (nativeLogicalImage_mono_depth V q hij)

theorem nativeDenseDepth_le_nat_iff (h : ℕ) :
    nativeDenseDepth V q ≤ (h : ℕ∞) ↔
      1 ≤ h ∧ (generatedLogicalSubgroup V q h).topologicalClosure = ⊤ := by
  apply positiveDepthInf_le_nat_iff
  intro i j hij hi
  apply top_unique
  rw [← hi]
  exact Subgroup.topologicalClosure_mono (generatedLogicalSubgroup_mono V q hij)

theorem nativeExactDepth_le_nat_iff (h : ℕ) :
    nativeExactDepth V q ≤ (h : ℕ∞) ↔ 1 ≤ h ∧ generatedLogicalSubgroup V q h = ⊤ := by
  apply positiveDepthInf_le_nat_iff
  intro i j hij hi
  apply top_unique
  rw [← hi]
  exact generatedLogicalSubgroup_mono V q hij

/-- The two lower bounds for exact generation hold independently of the geometric step. -/
theorem max_nativeCriticalDepth_nativeDenseDepth_le_nativeExactDepth (hK : 2 ≤ K) :
    max (nativeCriticalDepth V q) (nativeDenseDepth V q) ≤ nativeExactDepth V q := by
  let : Uncountable (PU (Fin K)) := nativePU_uncountable K hK
  apply max_le
  · apply positiveDepthInf_antitone
    intro h hExact hFinite
    exact subgroupClosure_ne_top_of_countable hFinite.countable hExact
  · apply positiveDepthInf_antitone
    intro h hExact
    apply top_unique
    rw [← hExact]
    exact (generatedLogicalSubgroup V q h).le_topologicalClosure

/-- Conditional on the identity-neighborhood step, the exact threshold is the maximum.
The premise is the geometric obligation at each positive depth with an infinite
alphabet and dense finite words. -/
theorem nativeExactDepth_eq_max_of_identity_neighborhood (hK : 2 ≤ K)
    (hGeometry : ∀ h : ℕ, 1 ≤ h → (nativeLogicalImage V q h).Infinite →
      (generatedLogicalSubgroup V q h).topologicalClosure = ⊤ →
        (generatedLogicalSubgroup V q h : Set (PU (Fin K))) ∈ 𝓝 1) :
    nativeExactDepth V q = max (nativeCriticalDepth V q) (nativeDenseDepth V q) := by
  apply le_antisymm _ (max_nativeCriticalDepth_nativeDenseDepth_le_nativeExactDepth V q hK)
  let H := max (nativeCriticalDepth V q) (nativeDenseDepth V q)
  change nativeExactDepth V q ≤ H
  by_cases hTop : H = ⊤
  · rw [hTop]
    exact le_top
  let h := H.lift (lt_top_iff_ne_top.mpr hTop)
  have hCast : (h : ℕ∞) = H := ENat.natCast_lift _ _
  have hInfinite := (nativeCriticalDepth_le_nat_iff V q h).mp
    (hCast.symm ▸ (le_max_left (nativeCriticalDepth V q) (nativeDenseDepth V q)))
  have hDense := (nativeDenseDepth_le_nat_iff V q h).mp
    (hCast.symm ▸ (le_max_right (nativeCriticalDepth V q) (nativeDenseDepth V q)))
  rw [← hCast]
  exact (nativeExactDepth_le_nat_iff V q h).mpr
    ⟨hInfinite.1, dense_subgroup_eq_top_of_one_nhds _ hDense.2
      (hGeometry h hInfinite.1 hInfinite.2 hDense.2)⟩

/-- The four-qubit code has onset at depth one and obeys the
dense-generation lower bound on its exact threshold. -/
theorem fourQubit_binary_generation_lower_bound :
    max (1 : ℕ∞) (nativeDenseDepth FourQubit.code.encoding 2) ≤
      nativeExactDepth FourQubit.code.encoding 2 := by
  have h := max_nativeCriticalDepth_nativeDenseDepth_le_nativeExactDepth
    FourQubit.code.encoding 2 (by decide)
  rw [nativeCriticalDepth_eq_legacy FourQubit.code.encoding FourQubit.encoding_isometry 2] at h
  have hCritical : hInfinityPositiveAtMost FourQubit.code 2 = (1 : ℕ∞) := by
    exact CriticalDepth.Manuscript.PositiveDepthExamples.fourQubit_positive_minimum_one
  simpa only [hCritical] using h

end CriticalDepth.ReviewV2
