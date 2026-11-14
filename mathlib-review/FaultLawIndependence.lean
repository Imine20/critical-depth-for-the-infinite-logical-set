import FaultExponent
import EncodedFaultRecovery

/-!
# Independence of fault exponents from positive conditional weights

The complete history set and the recovery class stay the same. Changing
the strictly positive conditional Pauli weights multiplies the mass of
each history by a positive constant independent of the failure rate.
The finite family of ratios bounds the optimized losses in both
directions.
-/

namespace CriticalDepth.FaultLawIndependence

noncomputable section

open Filter Set Asymptotics
open scoped BigOperators Topology
open FaultExponent FaultProbability IndependentFaultHistories

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
variable {Recovery : Type*} [Nonempty Recovery]

private def ratioBound (μ ν : Law Label) : ℝ :=
  1 + ∑ x : History Label, conditionalWeight μ x / conditionalWeight ν x

private theorem ratioBound_pos (μ ν : Law Label) : 0 < ratioBound μ ν := by
  unfold ratioBound
  have h : 0 ≤ ∑ x : History Label, conditionalWeight μ x / conditionalWeight ν x :=
    Finset.sum_nonneg fun x _ => div_nonneg
      (conditionalWeight_pos μ x).le (conditionalWeight_pos ν x).le
  linarith

private theorem mass_le_ratioBound (μ ν : Law Label)
    {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (x : History Label) :
    mass μ p x ≤ ratioBound μ ν * mass ν p x := by
  have hr : conditionalWeight μ x / conditionalWeight ν x ≤ ratioBound μ ν := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun y : History Label => conditionalWeight μ y / conditionalWeight ν y)
      (fun y _ => div_nonneg (conditionalWeight_pos μ y).le (conditionalWeight_pos ν y).le)
      (Finset.mem_univ x)
    unfold ratioBound
    linarith
  have hw : conditionalWeight μ x ≤ ratioBound μ ν * conditionalWeight ν x :=
    (div_le_iff₀ (conditionalWeight_pos ν x)).mp hr
  rw [mass_eq_historyMass, mass_eq_historyMass]
  unfold historyMass
  calc
    _ ≤ ((ratioBound μ ν * conditionalWeight ν x) * p ^ (faults x).card) *
        (1 - p) ^ (Fintype.card Loc - (faults x).card) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (pow_nonneg hp _))
        (pow_nonneg (sub_nonneg.mpr hp₁) _)
    _ = _ := by simp only [mul_assoc]

private theorem compare_lossAt (μ ν : Law Label) (loss : History Label → Recovery → ℝ)
    (hloss : ∀ x r, 0 ≤ loss x r) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (r : Recovery) :
    lossAt μ loss p r ≤ ratioBound μ ν * lossAt ν loss p r := by
  unfold lossAt Manuscript20261114.expectedHistoryLoss
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mass_le_ratioBound μ ν hp hp₁ x) (hloss x r)

private theorem compare_optimalLoss (μ ν : Law Label) (loss : History Label → Recovery → ℝ)
    (hloss : ∀ x r, 0 ≤ loss x r) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    optimalLoss μ loss p ≤ ratioBound μ ν * optimalLoss ν loss p := by
  have hr : 0 < ratioBound μ ν := ratioBound_pos μ ν
  have hb : BddBelow (range (lossAt μ loss p)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact Finset.sum_nonneg fun x _ => mul_nonneg (mass_nonneg μ hp hp₁ x) (hloss x r)
  have hDiv : optimalLoss μ loss p / ratioBound μ ν ≤ optimalLoss ν loss p := by
    unfold optimalLoss
    apply le_csInf (range_nonempty _)
    rintro _ ⟨r, rfl⟩
    apply (div_le_iff₀ hr).mpr
    rw [mul_comm (lossAt ν loss p r)]
    exact (csInf_le hb (mem_range_self r)).trans (compare_lossAt μ ν loss hloss hp hp₁ r)
  have h := (div_le_iff₀ hr).mp hDiv
  simpa only [mul_comm] using h

theorem optimalLoss_isBigO_of_positiveLaws (μ ν : Law Label)
    (loss : History Label → Recovery → ℝ) (hloss : ∀ x r, 0 ≤ loss x r) :
    optimalLoss μ loss =O[𝓝[>] (0 : ℝ)] optimalLoss ν loss := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨ratioBound μ ν, ?_⟩
  have hnear : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, by norm_num, subset_rfl⟩
  filter_upwards [hnear] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (optimalLoss_nonneg μ loss hloss hp.1.le hp.2.le),
    Real.norm_eq_abs, abs_of_nonneg (optimalLoss_nonneg ν loss hloss hp.1.le hp.2.le)]
  exact compare_optimalLoss μ ν loss hloss hp.1.le hp.2.le

/-- The integer exponent including infinity is the same for all strictly
positive native Pauli laws on the same fault labels. -/
theorem exponent_eq_of_positiveLaws (μ ν : Law Label) (loss : History Label → Recovery → ℝ)
    (hloss : ∀ x r, 0 ≤ loss x r) :
    exponent (optimalLoss μ loss) = exponent (optimalLoss ν loss) := by
  unfold exponent
  congr 1
  ext k
  constructor <;> rintro ⟨m, hm, hp⟩
  · exact ⟨m, hm, (optimalLoss_isBigO_of_positiveLaws ν μ loss hloss).trans hp⟩
  · exact ⟨m, hm, (optimalLoss_isBigO_of_positiveLaws μ ν loss hloss).trans hp⟩

theorem encodedExponent_eq_of_positiveLaws {Phys Log : Type*}
    [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]
    (μ ν : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    exponent (EncodedFaultRecovery.optimalInfidelity μ A) =
      exponent (EncodedFaultRecovery.optimalInfidelity ν A) :=
  exponent_eq_of_positiveLaws μ ν (fun x => EncodedFaultRecovery.branchLoss (A x))
    (fun x R => (EncodedFaultRecovery.branchLoss_mem_Icc (A x) (hA x) R).1)

#print axioms optimalLoss_isBigO_of_positiveLaws
#print axioms exponent_eq_of_positiveLaws
#print axioms encodedExponent_eq_of_positiveLaws

end

end CriticalDepth.FaultLawIndependence
