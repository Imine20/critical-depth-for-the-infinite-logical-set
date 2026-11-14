import FaultStabilizerPauliChannel
import FaultDiamondHistories
import FaultNativeModel

/-!
Optimal class decoding when the effective output noise of the same native
fault experiment is a stochastic Pauli channel.
-/

namespace CriticalDepth.FaultStabilizerPauliChannel

noncomputable section

open Matrix CriticalDepth.Manuscript CriticalDepth.PauliGroup
open CriticalDepth.FaultNativeModel CriticalDepth.FaultHistoryGeometry
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultCPTPRepresentation
open CriticalDepth.FaultChannelEffects CriticalDepth.FaultStabilizerLogicalBasis CriticalDepth.FaultStabilizerSyndrome
open CriticalDepth.IndependentFaultHistories
open scoped BigOperators

variable {n K q : ℕ} [Nonempty (Fin K × Fin 1)]

local instance : Fintype (PhysPauli n) := Fintype.ofFinite _

def nativeOutputError (L : Layers n q) (x : History (fun i : Location L => FaultLabel i)) :
    Operator (QubitBasis n) :=
  outputHistory (insertion L) physicalFault x (chronologicalFaults x)

def effectiveNativeNoise (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i))
    (p : ℝ) (X : Operator (QubitBasis n)) : Operator (QubitBasis n) :=
  ∑ x, (mass μ p x : ℂ) • (nativeOutputError L x * X * (nativeOutputError L x).conjTranspose)

def stochasticPhysicalPauliNoise (w : PhysPauli n → ℝ)
    (X : Operator (QubitBasis n)) : Operator (QubitBasis n) :=
  ∑ P, (w P : ℂ) • (P.val.val * X * P.val.val.conjTranspose)

def recoveredPhysicalPauliChannel (C : Code n (fun _ => 2) K 1) (w : PhysPauli n → ℝ)
    (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) :
    MatrixChannel (Fin K × Fin 1) (Fin K × Fin 1) :=
  ∑ P, (w P : ℂ) • recoverBranch R.val (encodedError C P)

theorem recoveredHistoryChannel_eq_physicalPauli
    (C : Code n (fun _ => 2) K 1) (L : Layers n q)
    (μ : Law (fun i : Location L => FaultLabel i)) (p : ℝ) (w : PhysPauli n → ℝ)
    (hNoise : effectiveNativeNoise L μ p = stochasticPhysicalPauliNoise w)
    (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) :
    recoveredHistoryChannel μ (encodedBranch C) p R = recoveredPhysicalPauliChannel C w R := by
  apply LinearMap.ext
  intro X
  have he := congrArg (fun Z : Operator (QubitBasis n) => R.val Z)
    (congrFun hNoise (C.encoding * X * C.encoding.conjTranspose))
  simpa only [effectiveNativeNoise, nativeOutputError, stochasticPhysicalPauliNoise,
    recoveredHistoryChannel, recoveredPhysicalPauliChannel, LinearMap.sum_apply,
    LinearMap.smul_apply, recoverBranch, LinearMap.coe_mk, AddHom.coe_mk,
    encodedError, encodedBranch, map_sum, map_smul, Matrix.conjTranspose_mul, Matrix.mul_assoc] using he

private theorem physicalPauliChannelLoss_eq_one_sub_fidelity
    (C : Code n (fun _ => 2) K 1) (w : PhysPauli n → ℝ) (hw : ∑ P, w P = 1)
    (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) :
    physicalPauliChannelLoss C w R = 1 - channelFidelity (recoveredPhysicalPauliChannel C w R) := by
  unfold physicalPauliChannelLoss channelBranchLoss channelFidelity recoveredPhysicalPauliChannel
  rw [amplify_sum]
  simp only [amplify_smul, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    smul_eq_mul, Finset.sum_div, mul_sub, mul_one, Finset.sum_sub_distrib, hw]
  congr 1
  apply Finset.sum_congr rfl
  intro P _
  ring

theorem exists_classMass_maximizer (C : Code n (fun _ => 2) K 1)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
    (w : PhysPauli n → ℝ) :
    ∃ selected : RealizedSyndrome S → LogicalClass C S,
      ∀ τ l, classMass C S hS w τ l ≤ classMass C S hS w τ (selected τ) := by
  classical
  have hNonempty : (Finset.univ : Finset (LogicalClass C S)).Nonempty :=
    ⟨Quotient.mk (logicalPauliSetoid C S) (Classical.choice inferInstance), Finset.mem_univ _⟩
  have he (τ : RealizedSyndrome S) : ∃ l : LogicalClass C S,
      ∀ j, classMass C S hS w τ j ≤ classMass C S hS w τ l := by
    obtain ⟨l, _, hl⟩ := Finset.exists_max_image Finset.univ (classMass C S hS w τ) hNonempty
    exact ⟨l, fun j => hl j (Finset.mem_univ _)⟩
  choose selected hselected using he
  exact ⟨selected, hselected⟩

/-- For stochastic Pauli output noise, the optimal entanglement infidelity
of the same fault experiment is the logical failure mass after choosing a
most likely class in every realized syndrome. -/
theorem nativePauliNoise_optimalInfidelity
    (C : Code n (fun _ => 2) K 1) (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i)) (p : ℝ)
    (w : PhysPauli n → ℝ) (hw : ∑ P, w P = 1)
    (hNoise : effectiveNativeNoise L μ p = stochasticPhysicalPauliNoise w) :
    ∃ selected : RealizedSyndrome S → LogicalClass C S,
      (∀ τ l, classMass C S hS w τ l ≤ classMass C S hS w τ (selected τ)) ∧
      circuitInfidelity C L μ p = 1 - ∑ τ, classMass C S hS w τ (selected τ) := by
  obtain ⟨selected, hs⟩ := exists_classMass_maximizer C S hS w
  refine ⟨selected, hs, ?_⟩
  change EncodedFaultRecovery.optimalInfidelity μ (encodedBranch C) p = _
  rw [optimalInfidelity_eq_cptp_inf]
  have hLoss : channelHistoryLoss μ (encodedBranch C) p = physicalPauliChannelLoss C w := by
    funext R
    rw [history_loss_eq_one_sub_fidelity,
      recoveredHistoryChannel_eq_physicalPauli C L μ p w hNoise R,
      physicalPauliChannelLoss_eq_one_sub_fidelity C w hw R]
  rw [hLoss, physicalPauliChannelLoss_optimum C S hS hspace w hw selected hs]

#print axioms recoveredHistoryChannel_eq_physicalPauli
#print axioms exists_classMass_maximizer
#print axioms nativePauliNoise_optimalInfidelity

end
end CriticalDepth.FaultStabilizerPauliChannel
