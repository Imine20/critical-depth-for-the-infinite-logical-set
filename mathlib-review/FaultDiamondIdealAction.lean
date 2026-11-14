import FaultDiamondHistories
import FaultDiamondFrame

/-! Comparison with the residual channel obtained by undoing the exact logical gate. -/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.Manuscript
open CriticalDepth.FaultCPTPRepresentation CriticalDepth.FaultCPTPOptimality
open CriticalDepth.IndependentFaultHistories
open scoped BigOperators

noncomputable section

variable {Phys Log Loc : Type*} [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

def undoIdealHistoryChannel (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (p : ℝ) (R : RecoveryChannel Phys Log) (W : Operator Log) : MatrixChannel Log Log :=
  (conjugateChannel W.conjTranspose).comp
    (recoveredHistoryChannel μ (fun x => A x * W) p R)

theorem undoIdealHistoryChannel_eq (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (p : ℝ) (R : RecoveryChannel Phys Log) (W : Operator Log) :
    undoIdealHistoryChannel μ A p R W =
      (conjugateChannel W.conjTranspose).comp
        ((recoveredHistoryChannel μ A p R).comp (conjugateChannel W)) := by
  apply congrArg ((conjugateChannel W.conjTranspose).comp)
  apply LinearMap.ext
  intro X
  simp only [recoveredHistoryChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, recoverBranch, conjugateChannel, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem undoIdealHistoryChannel_halfDiamond (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (R : RecoveryChannel Phys Log)
    (W : Operator Log) (hW : IsUnitary W) :
    halfDiamondByEffects (undoIdealHistoryChannel μ A p R W) =
      halfDiamondByEffects (recoveredHistoryChannel μ A p R) := by
  rw [undoIdealHistoryChannel_eq]
  have h := historyChannel_isCPTP μ A hA p hp hp₁ R
  exact halfDiamondByEffects_conjugateChannel W hW _ h.1 h.2

theorem optimalHistoryDiamond_eq_undoIdeal (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (W : Operator Log) (hW : IsUnitary W) :
    optimalHistoryDiamond μ A p =
      sInf (Set.range fun R => halfDiamondByEffects (undoIdealHistoryChannel μ A p R W)) := by
  unfold optimalHistoryDiamond
  congr 1
  apply congrArg Set.range
  funext R
  exact (undoIdealHistoryChannel_halfDiamond μ A hA p hp hp₁ R W hW).symm

#print axioms undoIdealHistoryChannel_halfDiamond
#print axioms optimalHistoryDiamond_eq_undoIdeal

end
end CriticalDepth.FaultChannelEffects
