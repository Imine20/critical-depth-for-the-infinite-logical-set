import FaultHistoryExperimentNormalization

/-!
The exact two-history lower bound of the manuscript. It holds pointwise
for arbitrary nonnegative history weights and all terminal CPTP recoveries.
-/

namespace CriticalDepth.FaultPointwiseAmbiguity

open Matrix
open CriticalDepth.EncodedFaultRecovery CriticalDepth.FaultCPTPOptimality
open CriticalDepth.IndependentFaultHistories
open scoped BigOperators

noncomputable section

variable {Phys Log : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]

/-- Two histories related by a traceless logical unitary up to phase
contribute at least their smaller weight to the optimal entanglement infidelity. -/
theorem minWeight_le_optimalCPTPInfidelity_of_ambiguous_pair
    {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (weight : Hist → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (x y : Hist) (hxy : x ≠ y) (P : Matrix Log Log ℂ)
    (hP : P * P.conjTranspose = 1) (htrace : P.trace = 0)
    (u : ℂ) (hu : ‖u‖ = 1) (hattach : A y = u • (A x * P)) :
    min (weight x) (weight y) ≤
      sInf (Set.range fun L : RecoveryChannel Phys Log =>
        ∑ z, weight z * channelBranchLoss (A z) L.val) := by
  have hunit : u * star u = 1 := by
    calc
      u * star u = (‖u‖ : ℂ) ^ 2 := Complex.mul_conj' u
      _ = 1 := by norm_num [hu]
  have hshiftedUnitary :
      (u • P) * (u • P).conjTranspose = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      hP, smul_smul, hunit, one_smul]
  have hshiftedTrace : (u • P).trace = 0 := by
    rw [Matrix.trace_smul, htrace, smul_zero]
  have hshiftedBranch : A y = A x * (u • P) := by
    simpa only [Matrix.mul_smul] using hattach
  apply le_csInf
  · obtain ⟨R⟩ := (inferInstance : Nonempty (TerminalRecovery Phys Log))
    exact ⟨_, Set.mem_range_self (fromKraus R)⟩
  rintro _ ⟨L, rfl⟩
  obtain ⟨R, rfl⟩ := fromKraus_surjective L
  have hloss (z : Hist) : 0 ≤ branchLoss (A z) R :=
    (branchLoss_mem_Icc (A z) (hA z) R).1
  have hambiguity : 1 ≤ branchLoss (A x) R + branchLoss (A y) R :=
    FaultAmbiguity.twoHistory_loss_sum_ge_one
      (A x) (A y) R.kraus (u • P) (hA x) R.complete hshiftedUnitary hshiftedTrace hshiftedBranch
  have hpair := FaultProbability.minMass_le_weightedInfidelity
    (weight x) (weight y) (branchLoss (A x) R) (branchLoss (A y) R)
    (hweight x) (hweight y) (hloss x) (hloss y) hambiguity
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun z => weight z * branchLoss (A z) R)
    (Finset.subset_univ ({x, y} : Finset Hist))
    (fun z _ _ => mul_nonneg (hweight z) (hloss z))
  apply hpair.trans
  simpa only [Finset.sum_pair hxy, fromKraus, channelBranchLoss_kraus, branchLoss] using hsum

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

theorem minMass_le_optimalInfidelity_of_ambiguous_pair (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (x y : History Label) (hxy : x ≠ y) (P : Matrix Log Log ℂ)
    (hP : P * P.conjTranspose = 1) (htrace : P.trace = 0)
    (u : ℂ) (hu : ‖u‖ = 1) (hattach : A y = u • (A x * P)) :
    min (mass μ p x) (mass μ p y) ≤ optimalInfidelity μ A p := by
  rw [optimalInfidelity_eq_cptp_inf]
  change min (mass μ p x) (mass μ p y) ≤
    sInf (Set.range fun L : RecoveryChannel Phys Log =>
      ∑ z, mass μ p z * channelBranchLoss (A z) L.val)
  exact minWeight_le_optimalCPTPInfidelity_of_ambiguous_pair A hA (mass μ p)
    (mass_nonneg μ hp hp₁) x y hxy P hP htrace u hu hattach

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization

/-- The same pointwise bound on the original native gate-list carrier. -/
theorem minMass_le_paperCircuitInfidelity_of_ambiguous_pair {n K q : ℕ}
    [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (L : PaperLayers (n := n) (q := q))
    (μ : Law (PaperLabel L)) (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (x y : History (PaperLabel L)) (hxy : x ≠ y)
    (P : Matrix (Fin K × Fin 1) (Fin K × Fin 1) ℂ)
    (hP : P * P.conjTranspose = 1) (htrace : P.trace = 0)
    (u : ℂ) (hu : ‖u‖ = 1)
    (hattach : paperEncodedBranch C L y = u • (paperEncodedBranch C L x * P)) :
    min (mass μ p x) (mass μ p y) ≤ paperCircuitInfidelity C L μ p := by
  apply minMass_le_optimalInfidelity_of_ambiguous_pair μ (paperEncodedBranch C L)
    _ p hp hp₁ x y hxy P hP htrace u hu hattach
  intro z
  rw [paperEncodedBranch_eq_native]
  exact encodedBranch_isometry C (historyEquiv L z)

#print axioms minWeight_le_optimalCPTPInfidelity_of_ambiguous_pair
#print axioms minMass_le_optimalInfidelity_of_ambiguous_pair
#print axioms minMass_le_paperCircuitInfidelity_of_ambiguous_pair

end

end CriticalDepth.FaultPointwiseAmbiguity
