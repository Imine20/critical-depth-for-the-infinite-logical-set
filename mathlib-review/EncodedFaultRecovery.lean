import FaultExponent
import FaultAmbiguity
import KnillLaflammeGram

/-!
Finite isometric fault branches and a common trace-preserving recovery.
The loss uses the normalized overlap with the maximally entangled state.
-/

namespace CriticalDepth.EncodedFaultRecovery

open Matrix Set
open scoped BigOperators ENat
open CriticalDepth.FaultEntanglementFidelity
open CriticalDepth.IndependentFaultHistories
open CriticalDepth.KnillLaflammeGram

noncomputable section

variable {Phys Log Loc : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

/-- A finite Kraus family defines a completely positive trace-preserving
terminal map from the physical register to the logical register. -/
structure TerminalRecovery (Phys Log : Type*) [Fintype Phys] [DecidableEq Phys]
    [Fintype Log] where
  count : ℕ
  kraus : Fin count → Matrix Log Phys ℂ
  complete : ∑ k, (kraus k).conjTranspose * kraus k = 1

instance : Nonempty (TerminalRecovery Phys Log) := by
  let A : Empty → Matrix Phys Log ℂ := fun x => x.elim
  obtain ⟨r, R, z, hTP, hz⟩ := existsRecoveryKraus_of_scalarCrossTerms A 0 (by
    intro x
    exact x.elim)
  exact ⟨⟨r, R, hTP⟩⟩

def branchLoss (A : Matrix Phys Log ℂ) (R : TerminalRecovery Phys Log) : ℝ :=
  loss fun k => R.kraus k * A

theorem composed_complete (A : Matrix Phys Log ℂ) (hA : A.conjTranspose * A = 1)
    (R : TerminalRecovery Phys Log) :
    ∑ k, (R.kraus k * A).conjTranspose * (R.kraus k * A) = 1 := by
  calc
    _ = A.conjTranspose * (∑ k, (R.kraus k).conjTranspose * R.kraus k) * A := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [R.complete, Matrix.mul_one, hA]

theorem branchLoss_mem_Icc (A : Matrix Phys Log ℂ) (hA : A.conjTranspose * A = 1)
    (R : TerminalRecovery Phys Log) : branchLoss A R ∈ Icc 0 1 :=
  ⟨loss_nonneg _ (composed_complete A hA R), loss_le_one _⟩

/-- The loss of a common recovery is zero on an isometric branch exactly
when all of its Kraus actions on that branch are scalar. -/
theorem branchLoss_eq_zero_iff (A : Matrix Phys Log ℂ) (hA : A.conjTranspose * A = 1)
    (R : TerminalRecovery Phys Log) :
    branchLoss A R = 0 ↔ ∀ k, ∃ z : ℂ, R.kraus k * A = z • (1 : Matrix Log Log ℂ) :=
  loss_eq_zero_iff _ (composed_complete A hA R)

theorem common_zero_loss_iff {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    (∃ R : TerminalRecovery Phys Log, ∀ x, branchLoss (A x) R = 0) ↔
      ∀ x y, ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ) := by
  classical
  constructor
  · rintro ⟨R, hR⟩ x y
    choose a ha using (branchLoss_eq_zero_iff (A x) (hA x) R).mp (hR x)
    choose b hb using (branchLoss_eq_zero_iff (A y) (hA y) R).mp (hR y)
    exact ⟨_, CriticalDepth.Manuscript20261114.crossTerm_scalar_of_recoveryKraus
      (A x) (A y) R.kraus a b R.complete ha hb⟩
  · intro h
    choose z hz using h
    obtain ⟨r, R, w, hR, hw⟩ := existsRecoveryKraus_of_scalarCrossTerms A z hz
    let receiver : TerminalRecovery Phys Log := ⟨r, R, hR⟩
    exact ⟨receiver, fun x => (branchLoss_eq_zero_iff (A x) (hA x) receiver).mpr
      (fun k => ⟨w k x, hw k x⟩)⟩

def optimalInfidelity (μ : Law Label) (A : History Label → Matrix Phys Log ℂ) : ℝ → ℝ :=
  FaultExponent.optimalLoss μ (fun x => branchLoss (A x))

theorem guaranteed_exponent_of_scalarCrossTerms (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (m : ℕ)
    (hs : ∀ x y, (faults x).card < m → (faults y).card < m →
      ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    (m : ℕ∞) ≤ FaultExponent.exponent (optimalInfidelity μ A) := by
  classical
  let Good := {x : History Label // (faults x).card < m}
  let E : Good → Matrix Phys Log ℂ := fun x => A x.val
  obtain ⟨R, hR⟩ := (common_zero_loss_iff E (fun x => hA x.val)).mpr
    (fun x y => hs x.val y.val x.property y.property)
  exact FaultExponent.guaranteed_exponent μ _ m
    (fun x R' => branchLoss_mem_Icc (A x) (hA x) R') R
    (fun x hx => hR ⟨x, hx⟩)

theorem ambiguous_exponent_of_traceless_unitary (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (x y : History Label) (hxy : x ≠ y) (P : Matrix Log Log ℂ)
    (hP : P * P.conjTranspose = 1) (ht : P.trace = 0) (hattach : A y = A x * P) :
    FaultExponent.exponent (optimalInfidelity μ A) ≤
      ((max (faults x).card (faults y).card : ℕ) : ℕ∞) := by
  apply FaultExponent.ambiguous_exponent μ _
    (fun z r => (branchLoss_mem_Icc (A z) (hA z) r).1) x y hxy
  intro R
  exact FaultAmbiguity.twoHistory_loss_sum_ge_one
    (A x) (A y) R.kraus P (hA x) R.complete hP ht hattach

#print axioms ambiguous_exponent_of_traceless_unitary
#print axioms composed_complete
#print axioms branchLoss_eq_zero_iff
#print axioms common_zero_loss_iff
#print axioms guaranteed_exponent_of_scalarCrossTerms

end
end CriticalDepth.EncodedFaultRecovery
