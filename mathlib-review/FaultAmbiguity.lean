import FaultEntanglementFidelity

/-!
# Two histories differing by a traceless logical unitary

If two encoded histories differ by a traceless logical unitary, a common
terminal recovery gives total conditional entanglement infidelity at
least one. The inequality is Hilbert–Schmidt Bessel on the two unitary
directions; no restriction on the recovery Kraus operators is made.
-/

namespace CriticalDepth.FaultAmbiguity

noncomputable section

open Matrix
open FaultEntanglementFidelity
open scoped BigOperators ComplexOrder

variable {Phys Log Rec : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Fintype Rec]

private theorem twoUnitaryTraces_le [Nonempty Log] (P A : Matrix Log Log ℂ)
    (hP : P * P.conjTranspose = 1) (htrace : P.trace = 0) :
    Complex.normSq A.trace + Complex.normSq (A * P).trace ≤
      (Fintype.card Log : ℝ) * (A.conjTranspose * A).trace.re := by
  let D := (Fintype.card Log : ℂ)
  let a := A.trace / D
  let b := (A * P).trace / D
  let B := A - a • (1 : Matrix Log Log ℂ) - b • P.conjTranspose
  have hD : D ≠ 0 := by
    change (Fintype.card Log : ℂ) ≠ 0
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Log).ne'
  have hDreal : 0 < (Fintype.card Log : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Log)
  have hdstar : star D = D := by simp [D]
  have hPA : (P * A).trace = (A * P).trace := Matrix.trace_mul_comm _ _
  have hAP : (A.conjTranspose * P.conjTranspose).trace = star (A * P).trace := by
    rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, hPA]
  have hPtrace : P.conjTranspose.trace = 0 := by simp [htrace]
  have hExpand : (B.conjTranspose * B).trace = (A.conjTranspose * A).trace -
      ((Complex.normSq A.trace : ℂ) + (Complex.normSq (A * P).trace : ℂ)) / D := by
    simp only [B, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      smul_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_conjTranspose,
      smul_eq_mul, hP, Matrix.trace_one, hPA, hAP, htrace, star_zero, mul_zero]
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    change _ = (A.conjTranspose * A).trace -
      (star A.trace * A.trace + star (A * P).trace * (A * P).trace) / D
    simp only [a, b, star_div₀, hdstar]
    field_simp [hD]
    <;> ring
  have hnonneg := (Complex.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self B).trace_nonneg).1
  rw [hExpand] at hnonneg
  have hre : 0 ≤ (A.conjTranspose * A).trace.re -
      (Complex.normSq A.trace + Complex.normSq (A * P).trace) / (Fintype.card Log : ℝ) := by
    simpa only [D, Complex.sub_re, ← Complex.ofReal_add, ← Complex.ofReal_natCast,
      Complex.div_ofReal_re, Complex.ofReal_re] using hnonneg
  have h := (div_le_iff₀ hDreal).mp (sub_nonneg.mp hre)
  simpa only [mul_comm] using h

/-- Both error histories are correctable only if they have no traceless
logical ambiguity. For a common CPTP Kraus representation, their two
conditional infidelities together are at least one. -/
theorem twoHistory_loss_sum_ge_one [Nonempty Log]
    (A₀ A₁ : Matrix Phys Log ℂ) (R : Rec → Matrix Log Phys ℂ)
    (P : Matrix Log Log ℂ) (hA₀ : A₀.conjTranspose * A₀ = 1)
    (hR : (∑ i, (R i).conjTranspose * R i) = 1)
    (hP : P * P.conjTranspose = 1) (htrace : P.trace = 0)
    (hA₁ : A₁ = A₀ * P) :
    1 ≤ loss (fun i => R i * A₀) + loss (fun i => R i * A₁) := by
  let D := (Fintype.card Log : ℝ)
  have hD : 0 < D := by
    change 0 < (Fintype.card Log : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Log)
  have hTP : (∑ i, (R i * A₀).conjTranspose * (R i * A₀)) = 1 := by
    calc
      _ = A₀.conjTranspose * (∑ i, (R i).conjTranspose * R i) * A₀ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hR, Matrix.mul_one, hA₀]
  have hsum : (∑ i, ((R i * A₀).conjTranspose * (R i * A₀)).trace.re) = D := by
    have hp := congrArg (fun A : Matrix Log Log ℂ => A.trace.re) hTP
    simpa [D, Matrix.trace_sum, Complex.re_sum] using hp
  have hbd :
      (∑ i, Complex.normSq (R i * A₀).trace) + (∑ i, Complex.normSq (R i * A₁).trace)
        ≤ D ^ 2 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ i, D * ((R i * A₀).conjTranspose * (R i * A₀)).trace.re := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [hA₁, Matrix.mul_assoc] using twoUnitaryTraces_le P (R i * A₀) hP htrace
      _ = D ^ 2 := by rw [← Finset.mul_sum, hsum, pow_two]
  change 1 ≤ (1 - (∑ i, Complex.normSq (R i * A₀).trace) / D ^ 2) +
    (1 - (∑ i, Complex.normSq (R i * A₁).trace) / D ^ 2)
  have hsplit : ((∑ i, Complex.normSq (R i * A₀).trace) / D ^ 2) +
      ((∑ i, Complex.normSq (R i * A₁).trace) / D ^ 2) =
      ((∑ i, Complex.normSq (R i * A₀).trace) + (∑ i, Complex.normSq (R i * A₁).trace)) / D ^ 2 := by
    rw [add_div]
  have hu : ((∑ i, Complex.normSq (R i * A₀).trace) + (∑ i, Complex.normSq (R i * A₁).trace)) / D ^ 2 ≤ 1 :=
    (div_le_iff₀ (pow_pos hD 2)).mpr (by simpa only [one_mul] using hbd)
  linarith

#print axioms twoHistory_loss_sum_ge_one

end

end CriticalDepth.FaultAmbiguity
