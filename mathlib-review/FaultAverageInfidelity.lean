import FaultEntanglementFidelity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Average infidelity from the normalized fourth coordinate moment

The probability measure is assumed to have the fourth moment of the
unitarily invariant probability distribution on unit vectors. This file
derives the average-fidelity identity from that moment, without assuming
that fourth moment for a particular construction of Haar measure.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open Matrix MeasureTheory
open FaultEntanglementFidelity
open scoped BigOperators ComplexOrder

variable {Ω Log Rec : Type*} [MeasurableSpace Ω]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log] [Fintype Rec]

/-- Index the two copies of the matrix entry by pairs of logical coordinates. -/
def fourthTerm (v : Ω → Log → ℂ) (p q : Log × Log) (x : Ω) : ℂ :=
  (v x p.1 * star (v x p.2)) * (star (v x q.1) * v x q.2)

def fourthMoment (p q : Log × Log) : ℂ :=
  ((if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0) +
    (if p = q then 1 else 0)) /
    ((Fintype.card Log : ℂ) * ((Fintype.card Log : ℂ) + 1))

def pureOverlap (A : Matrix Log Log ℂ) (v : Log → ℂ) : ℂ :=
  star v ⬝ᵥ (A *ᵥ v)

def averageInfidelity (μ : Measure Ω) (v : Ω → Log → ℂ)
    (K : Rec → Matrix Log Log ℂ) : ℝ :=
  1 - ∫ x, ∑ k, Complex.normSq (pureOverlap (K k) (v x)) ∂μ

private theorem normSq_overlap_eq_sum (A : Matrix Log Log ℂ) (v : Ω → Log → ℂ) (x : Ω) :
    (Complex.normSq (pureOverlap A (v x)) : ℂ) =
      ∑ p : Log × Log, ∑ q : Log × Log,
        (star (A p.1 p.2) * A q.1 q.2) * fourthTerm v p q x := by
  have hx : pureOverlap A (v x) =
      ∑ p : Log × Log, star (v x p.1) * A p.1 p.2 * v x p.2 := by
    simp only [pureOverlap, Matrix.mulVec, dotProduct, Finset.mul_sum, Fintype.sum_prod_type,
      Pi.star_apply, mul_assoc]
  rw [Complex.normSq_eq_conj_mul_self, hx]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  change (star (star (v x p.1)) * star (A p.1 p.2) * star (v x p.2)) *
    (star (v x q.1) * A q.1 q.2 * v x q.2) = _
  rw [star_star]
  unfold fourthTerm
  ring

private theorem sum_moment_contraction (A : Matrix Log Log ℂ) :
    (∑ p : Log × Log, ∑ q : Log × Log,
      (star (A p.1 p.2) * A q.1 q.2) * fourthMoment p q) =
      ((Complex.normSq A.trace : ℂ) + (A.conjTranspose * A).trace) /
        ((Fintype.card Log : ℂ) * ((Fintype.card Log : ℂ) + 1)) := by
  classical
  let D : ℂ := (Fintype.card Log : ℂ) * ((Fintype.card Log : ℂ) + 1)
  let C (p q : Log × Log) := star (A p.1 p.2) * A q.1 q.2
  let f (p q : Log × Log) := if p.1 = p.2 ∧ q.1 = q.2 then C p q else 0
  let g (p q : Log × Log) := if p = q then C p q else 0
  have hsplit (p q : Log × Log) :
      C p q * fourthMoment p q = (f p q + g p q) / D := by
    change C p q * (((if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0) +
        (if p = q then (1 : ℂ) else 0)) / D) = _
    rw [← mul_div_assoc, mul_add]
    unfold f g
    split_ifs <;> simp only [mul_one, mul_zero]
  have hf : (∑ p : Log × Log, ∑ q : Log × Log, f p q) =
      (Complex.normSq A.trace : ℂ) := by
    have hInner (p : Log × Log) : (∑ q : Log × Log, f p q) =
        if p.1 = p.2 then star (A p.1 p.2) * A.trace else 0 := by
      by_cases hp : p.1 = p.2
      · simp only [f, hp, true_and, ite_true, Fintype.sum_prod_type]
        have hrow (i : Log) : (∑ j : Log, if i = j then C p (i, j) else 0) = C p (i, i) := by simp
        calc
          (∑ i : Log, ∑ j : Log, if i = j then C p (i, j) else 0) =
              ∑ i : Log, C p (i, i) := Finset.sum_congr rfl (fun i _ => hrow i)
          _ = _ := by
            simp only [C, Matrix.trace, Matrix.diag_apply, hp, Finset.mul_sum]
      · simp [f, hp]
    simp only [hInner, Fintype.sum_prod_type, Complex.normSq_eq_conj_mul_self,
      Matrix.trace, Matrix.diag_apply, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hg : (∑ p : Log × Log, ∑ q : Log × Log, g p q) =
      (A.conjTranspose * A).trace := by
    have hInner (p : Log × Log) : (∑ q : Log × Log, g p q) = C p p := by simp [g]
    simp only [hInner, C, Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.sum_comm
  change (∑ p : Log × Log, ∑ q : Log × Log, C p q * fourthMoment p q) =
    ((Complex.normSq A.trace : ℂ) + (A.conjTranspose * A).trace) / D
  simp only [hsplit, ← Finset.sum_div, Finset.sum_add_distrib, hf, hg]

theorem integral_single_pureOverlap (μ : Measure Ω) (v : Ω → Log → ℂ)
    (hI : ∀ p q, Integrable (fourthTerm v p q) μ)
    (hM : ∀ p q, (∫ x, fourthTerm v p q x ∂μ) = fourthMoment p q)
    (A : Matrix Log Log ℂ) :
    (∫ x, Complex.normSq (pureOverlap A (v x)) ∂μ) =
      (Complex.normSq A.trace + (A.conjTranspose * A).trace.re) /
        ((Fintype.card Log : ℝ) * ((Fintype.card Log : ℝ) + 1)) := by
  have hC : (∫ x, (Complex.normSq (pureOverlap A (v x)) : ℂ) ∂μ) =
      ((Complex.normSq A.trace : ℂ) + (A.conjTranspose * A).trace) /
        ((Fintype.card Log : ℂ) * ((Fintype.card Log : ℂ) + 1)) := by
    simp_rw [normSq_overlap_eq_sum]
    rw [integral_finsetSum]
    · simp_rw [integral_finsetSum _ (fun q _ => (hI _ q).const_mul _),
        integral_const_mul, hM]
      exact sum_moment_contraction A
    · intro p _
      exact integrable_finsetSum _ (fun q _ => (hI p q).const_mul _)
  have hr := congrArg Complex.re hC
  simpa only [integral_complex_ofReal, Complex.ofReal_re, ← Complex.ofReal_natCast,
    ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul,
    Complex.div_ofReal_re, Complex.add_re] using hr

/-- Eq. (S11) follows from the Haar coordinate moment for every
trace-preserving finite Kraus representation. -/
theorem averageInfidelity_eq_dim_ratio_loss (μ : Measure Ω) (v : Ω → Log → ℂ)
    (hI : ∀ p q, Integrable (fourthTerm v p q) μ)
    (hM : ∀ p q, (∫ x, fourthTerm v p q x ∂μ) = fourthMoment p q)
    (K : Rec → Matrix Log Log ℂ)
    (hTP : (∑ k, (K k).conjTranspose * K k) = 1) :
    averageInfidelity μ v K =
      ((Fintype.card Log : ℝ) / ((Fintype.card Log : ℝ) + 1)) * loss K := by
  let D := (Fintype.card Log : ℝ)
  have hD : 0 < D := by
    change 0 < (Fintype.card Log : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Log)
  have hD1 : D + 1 ≠ 0 := by linarith
  have htrace : (∑ k, ((K k).conjTranspose * K k).trace.re) = D := by
    have h := congrArg (fun A : Matrix Log Log ℂ => A.trace.re) hTP
    simpa [D, Matrix.trace_sum, Complex.re_sum] using h
  have hNormInt (A : Matrix Log Log ℂ) :
      Integrable (fun x => Complex.normSq (pureOverlap A (v x))) μ := by
    have hC : Integrable (fun x => (Complex.normSq (pureOverlap A (v x)) : ℂ)) μ := by
      simp_rw [normSq_overlap_eq_sum]
      exact integrable_finsetSum _ (fun p _ =>
        integrable_finsetSum _ (fun q _ => (hI p q).const_mul _))
    simpa using hC.re
  unfold averageInfidelity
  rw [integral_finsetSum _ (fun k _ => hNormInt (K k))]
  simp only [integral_single_pureOverlap μ v hI hM, ← Finset.sum_div, Finset.sum_add_distrib,
    loss, fidelity]
  change 1 - ((∑ k, Complex.normSq (K k).trace) + (∑ k, ((K k).conjTranspose * K k).trace.re))
    / (D * (D + 1)) = D / (D + 1) * (1 - (∑ k, Complex.normSq (K k).trace) / D ^ 2)
  rw [htrace]
  field_simp [hD.ne', hD1] <;> ring

#print axioms integral_single_pureOverlap
#print axioms averageInfidelity_eq_dim_ratio_loss

end

end CriticalDepth.FaultAverageInfidelity
