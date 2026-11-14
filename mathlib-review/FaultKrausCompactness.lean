import FaultEntanglementFidelity
import Mathlib.Analysis.Matrix.Normed

/-!
# Compact recovery models with a finite Kraus index

Trace-preserving rectangular Kraus families with a prescribed finite
index form a compact space. This suffices to attain the infidelity
minimum over that model.
-/

namespace CriticalDepth.FaultKrausCompactness

noncomputable section

open Matrix
open scoped BigOperators Topology Matrix.Norms.Elementwise

variable {Phys Log Rec : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Fintype Rec]

/-- Families of rectangular Kraus operators obeying trace preservation. -/
def tpFamilies : Set (Rec → Matrix Log Phys ℂ) :=
  {R | (∑ i, (R i).conjTranspose * R i) = 1}

private theorem continuous_entry (i : Rec) (j : Log) (a : Phys) :
    Continuous (fun R : Rec → Matrix Log Phys ℂ => R i j a) := by
  have h₁ : Continuous (fun R : Rec → Matrix Log Phys ℂ => R i) := continuous_apply i
  have h₂ : Continuous (fun A : Matrix Log Phys ℂ => A j) := continuous_apply j
  have h₃ : Continuous (fun v : Phys → ℂ => v a) := continuous_apply a
  exact h₃.comp (h₂.comp h₁)

theorem isClosed_tpFamilies :
    IsClosed (tpFamilies (Phys := Phys) (Log := Log) (Rec := Rec)) := by
  apply isClosed_eq _ continuous_const
  apply continuous_finsetSum
  intro i _
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact continuous_finsetSum _ fun j _ => (continuous_entry i j a).star.mul
    (continuous_entry i j b)

private theorem norm_entry_le_one (R : Rec → Matrix Log Phys ℂ)
    (hR : R ∈ tpFamilies) (k : Rec) (j : Log) (a : Phys) :
    ‖R k j a‖ ≤ 1 := by
  have hc : (∑ i : Rec, ∑ b : Log, Complex.normSq (R i b a)) = 1 := by
    have h := congrArg (fun H : Matrix Phys Phys ℂ => (H a a).re) hR
    have hentry (z : ℂ) : (star z * z).re = Complex.normSq z := by
      change ((starRingEnd ℂ) z * z).re = Complex.normSq z
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, hentry, Matrix.one_apply_eq, Complex.one_re] using h
  have h₁ : Complex.normSq (R k j a) ≤ ∑ b : Log, Complex.normSq (R k b a) :=
    Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (R k b a)) (Finset.mem_univ j)
  have h₂ : (∑ b : Log, Complex.normSq (R k b a)) ≤
      ∑ i : Rec, ∑ b : Log, Complex.normSq (R i b a) :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg (R i b a))
      (Finset.mem_univ k)
  have h := h₁.trans h₂
  rw [hc, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (R k j a)]

/-- The operator tensor coordinates are bounded solely by trace
preservation, so the result applies also to arbitrary finite recovery
indices larger than the minimal Choi rank. -/
theorem isCompact_tpFamilies :
    IsCompact (tpFamilies (Phys := Phys) (Log := Log) (Rec := Rec)) := by
  apply (isCompact_closedBall (0 : Rec → Matrix Log Phys ℂ) 1).of_isClosed_subset isClosed_tpFamilies
  intro R hR
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  exact (Matrix.norm_le_iff zero_le_one).mpr (fun j a => norm_entry_le_one R hR k j a)

/-- The conditional loss of the recovered encoded branch is continuous
as a polynomial in the real and imaginary parts of the Kraus entries. -/
theorem continuous_encodedLoss (A : Matrix Phys Log ℂ) :
    Continuous (fun R : Rec → Matrix Log Phys ℂ =>
      FaultEntanglementFidelity.loss (fun i => R i * A)) := by
  unfold FaultEntanglementFidelity.loss FaultEntanglementFidelity.fidelity
  apply continuous_const.sub
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply Complex.continuous_normSq.comp
  unfold Matrix.trace
  apply continuous_finsetSum
  intro j _
  unfold Matrix.diag
  simp only [Matrix.mul_apply]
  apply continuous_finsetSum
  intro a _
  exact (continuous_entry i j a).mul continuous_const

/-- If at least one trace-preserving family exists at this size, any
finite weighted history loss attains its minimum in that model. -/
theorem exists_minimum_historyLoss {Hist : Type*} (S : Finset Hist) (w : Hist → ℝ)
    (A : Hist → Matrix Phys Log ℂ)
    (hne : (tpFamilies (Phys := Phys) (Log := Log) (Rec := Rec)).Nonempty) :
    ∃ R ∈ tpFamilies, ∀ T ∈ tpFamilies,
      (∑ i ∈ S, w i * FaultEntanglementFidelity.loss (fun k : Rec => R k * A i)) ≤
        ∑ i ∈ S, w i * FaultEntanglementFidelity.loss (fun k : Rec => T k * A i) := by
  have hcont : Continuous (fun R : Rec → Matrix Log Phys ℂ =>
      ∑ i ∈ S, w i * FaultEntanglementFidelity.loss (fun k : Rec => R k * A i)) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_encodedLoss (A i))
  exact isCompact_tpFamilies.exists_isMinOn hne hcont.continuousOn

#print axioms isCompact_tpFamilies
#print axioms continuous_encodedLoss
#print axioms exists_minimum_historyLoss

end

end CriticalDepth.FaultKrausCompactness
