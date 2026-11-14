import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114

/-- Expected loss for a finite collection of fault histories. -/
noncomputable def expectedHistoryLoss {H : Type*} (histories : Finset H)
    (probability loss : H → ℝ) : ℝ :=
  ∑ x ∈ histories, probability x * loss x

/-- Histories exactly corrected by the same recovery make no contribution. -/
theorem expectedHistoryLoss_le_badMass {H : Type*} [DecidableEq H]
    {all good : Finset H} (probability loss : H → ℝ)
    (hprob : ∀ x ∈ all, 0 ≤ probability x)
    (hloss : ∀ x ∈ all, loss x ≤ 1)
    (hgood : ∀ x ∈ good, loss x = 0) :
    expectedHistoryLoss all probability loss ≤ ∑ x ∈ all \ good, probability x := by
  unfold expectedHistoryLoss
  have heq : ∑ x ∈ all, probability x * loss x =
      ∑ x ∈ all \ good, probability x * loss x := by
    symm
    apply Finset.sum_subset Finset.sdiff_subset
    intro x hxa hx
    have hxg : x ∈ good := by
      by_contra h
      exact hx (Finset.mem_sdiff.mpr ⟨hxa, h⟩)
    rw [hgood x hxg, mul_zero]
  rw [heq]
  apply Finset.sum_le_sum
  intro x hx
  have hxa := (Finset.mem_sdiff.mp hx).1
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hloss x hxa) (hprob x hxa)

/-- A set of histories with uniformly positive probability and total loss contributes
a uniform lower bound, including when the recovery depends on the noise strength. -/
theorem expectedHistoryLoss_ge_weightedSubset {H : Type*}
    {all bad : Finset H} (hsub : bad ⊆ all) (probability loss : H → ℝ) {w L : ℝ}
    (hw : 0 ≤ w) (hprob : ∀ x ∈ all, 0 ≤ probability x)
    (hloss : ∀ x ∈ all, 0 ≤ loss x)
    (hweight : ∀ x ∈ bad, w ≤ probability x) (hbad : L ≤ ∑ x ∈ bad, loss x) :
    w * L ≤ expectedHistoryLoss all probability loss := by
  calc
    w * L ≤ w * ∑ x ∈ bad, loss x := mul_le_mul_of_nonneg_left hbad hw
    _ = ∑ x ∈ bad, w * loss x := Finset.mul_sum ..
    _ ≤ ∑ x ∈ bad, probability x * loss x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hweight x hx) (hloss x (hsub hx))
    _ ≤ expectedHistoryLoss all probability loss := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx _
      exact mul_nonneg (hprob x hx) (hloss x hx)

/-- Compactness turns failure of a common exact recovery into a strictly
positive uniform loss over the selected histories. The compactness and
continuity assumptions are to be supplied by the chosen channel model. -/
theorem uniformLoss_of_no_common_zero {H R : Type*} [TopologicalSpace R]
    (histories : Finset H) (recoveries : Set R) (loss : H → R → ℝ)
    (hcompact : IsCompact recoveries) (hnonempty : recoveries.Nonempty)
    (hcontinuous : ∀ x ∈ histories, ContinuousOn (loss x) recoveries)
    (hnonneg : ∀ r ∈ recoveries, ∀ x ∈ histories, 0 ≤ loss x r)
    (hnot : ∀ r ∈ recoveries, ∃ x ∈ histories, 0 < loss x r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ recoveries, c ≤ ∑ x ∈ histories, loss x r := by
  have hsumContinuous :
      ContinuousOn (fun r => ∑ x ∈ histories, loss x r) recoveries :=
    continuousOn_finsetSum _ hcontinuous
  obtain ⟨r₀, hr₀, hmin⟩ := hcompact.exists_isMinOn hnonempty hsumContinuous
  obtain ⟨x, hx, hpositive⟩ := hnot r₀ hr₀
  refine ⟨∑ x ∈ histories, loss x r₀, ?_, hmin⟩
  exact hpositive.trans_le (Finset.single_le_sum (hnonneg r₀ hr₀) hx)

#print axioms expectedHistoryLoss_le_badMass
#print axioms expectedHistoryLoss_ge_weightedSubset
#print axioms uniformLoss_of_no_common_zero

end CriticalDepth.Manuscript20261114
