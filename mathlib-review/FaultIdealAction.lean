import FaultNativeCeiling

/-!
Reference-frame comparison for an exact noiseless logical implementation.
The ideal decoded inverse cancels the ideal logical gate inside each
Kraus trace, even when the fault propagation is not a Pauli channel.
-/

namespace CriticalDepth.FaultIdealAction

open CriticalDepth.EncodedFaultRecovery CriticalDepth.FaultEntanglementFidelity
open CriticalDepth.IndependentFaultHistories
open scoped BigOperators

noncomputable section

variable {Phys Log Rec : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log]
variable [Fintype Rec]

theorem trace_of_conjugated_branch (T : Matrix Log Log ℂ)
    (hT : T * T.conjTranspose = 1)
    (A : Matrix Phys Log ℂ) (R : Matrix Log Phys ℂ) :
    (T.conjTranspose * (R * A * T)).trace = (R * A).trace := by
  calc
    _ = ((R * A * T) * T.conjTranspose).trace := Matrix.trace_mul_comm _ _
    _ = (R * A).trace := by rw [Matrix.mul_assoc, hT, Matrix.mul_one]

/-- Undo the exact noiseless logical unitary at the output. The resulting
entanglement infidelity equals the loss in the encoding's logical frame. -/
theorem loss_of_undoing_ideal_action (T : Matrix Log Log ℂ)
    (hT : T * T.conjTranspose = 1)
    (A : Matrix Phys Log ℂ) (R : Rec → Matrix Log Phys ℂ) :
    loss (fun i => T.conjTranspose * (R i * (A * T))) = loss (fun i => R i * A) := by
  unfold loss fidelity
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (T.conjTranspose * (R i * (A * T))).trace = (R i * A).trace
  rw [← Matrix.mul_assoc (R i) A T]
  exact trace_of_conjugated_branch T hT A (R i)

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
variable [Nonempty Log]

theorem optimalInfidelity_eq_undoing_ideal_action
    (μ : Law Label) (T : Matrix Log Log ℂ) (hT : T * T.conjTranspose = 1)
    (A : History Label → Matrix Phys Log ℂ) (p : ℝ) :
    optimalInfidelity μ A p =
      sInf (Set.range fun R : TerminalRecovery Phys Log =>
        ∑ x, mass μ p x * loss (fun k => T.conjTranspose * (R.kraus k * (A x * T)))) := by
  unfold optimalInfidelity FaultExponent.optimalLoss
  congr 1
  apply congrArg Set.range
  funext R
  simp only [FaultExponent.lossAt, Manuscript20261114.expectedHistoryLoss, branchLoss,
    loss_of_undoing_ideal_action T hT]

#print axioms loss_of_undoing_ideal_action
#print axioms optimalInfidelity_eq_undoing_ideal_action

end
end CriticalDepth.FaultIdealAction
