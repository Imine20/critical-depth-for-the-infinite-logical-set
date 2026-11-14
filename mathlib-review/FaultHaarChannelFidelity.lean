import FaultHaarComplexMoment
import FaultDiamondHistories

/-!
Average logical infidelity for the same terminal CPTP channels as
entanglement infidelity. The input is averaged over the spherical Haar probability.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open Matrix MeasureTheory Asymptotics Filter
open CriticalDepth.FaultEntanglementFidelity CriticalDepth.FaultCPTPRepresentation
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultChannelEffects
open CriticalDepth.FaultProbability CriticalDepth.IndependentFaultHistories
open scoped BigOperators

variable {Phys Log : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]

abbrev fidelityDimensionRatio (Log : Type*) [Fintype Log] : ℝ :=
  (Fintype.card Log : ℝ) / ((Fintype.card Log : ℝ) + 1)

theorem fidelityDimensionRatio_pos (Log : Type*) [Fintype Log] [Nonempty Log] :
    0 < fidelityDimensionRatio Log := by positivity

/-- Haar averaging of the same physical terminal channel after undoing its
ideal logical action over the reference coordinates. -/
def channelAverageInfidelity (L : MatrixChannel Log Log) : ℝ :=
  1 - ∫ x : LogicalSphere Log,
    (star (logicalSphereVector x) ⬝ᵥ
      (L (vecMulVec (logicalSphereVector x) (star (logicalSphereVector x))) *ᵥ
        logicalSphereVector x)).re ∂sphereHaar (EuclideanSpace ℝ (Log × Bool))

private theorem pure_projector_expectation (M : Matrix Log Log ℂ) (v : Log → ℂ) :
    (star v ⬝ᵥ ((M * vecMulVec v (star v) * M.conjTranspose) *ᵥ v)).re =
      Complex.normSq (pureOverlap M v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
  let w := M *ᵥ v
  let z := star v ⬝ᵥ w
  change (star v ⬝ᵥ (vecMulVec w (star w) *ᵥ v)).re = Complex.normSq z
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, star_dotProduct w v]
  change (z * star z).re = Complex.normSq z
  rw [mul_comm]
  change ((starRingEnd ℂ) z * z).re = Complex.normSq z
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

private theorem channelAverageInfidelity_eq_kraus {Rec : Type*} [Fintype Rec]
    (K : Rec → Matrix Log Log ℂ) :
    channelAverageInfidelity (krausMap K) =
      averageInfidelity (sphereHaar (EuclideanSpace ℝ (Log × Bool))) logicalSphereVector K := by
  unfold channelAverageInfidelity averageInfidelity
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  let v := logicalSphereVector x
  change (star v ⬝ᵥ (krausMap K (vecMulVec v (star v)) *ᵥ v)).re =
    ∑ k, Complex.normSq (pureOverlap (K k) v)
  rw [krausMap_apply, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => pure_projector_expectation (K k) v

theorem channelAverageInfidelity_eq_dim_ratio_fidelity
    (L : RecoveryChannel Log Log) :
    channelAverageInfidelity L.val = fidelityDimensionRatio Log * (1 - channelFidelity L.val) := by
  obtain ⟨K, hK, hTP⟩ := (cptp_iff_exists_completeKraus L.val).mp L.property
  rw [hK, channelAverageInfidelity_eq_kraus, channelFidelity_kraus,
    averageInfidelity_sphereHaar_eq_dim_ratio_loss K hTP]
  rfl

theorem channelAverageBranch_eq_dim_ratio_loss
    (R : RecoveryChannel Phys Log) (A : Matrix Phys Log ℂ)
    (hA : A.conjTranspose * A = 1) :
    channelAverageInfidelity (recoverBranch R.val A) =
      fidelityDimensionRatio Log * channelBranchLoss A R.val := by
  let L : RecoveryChannel Log Log :=
    ⟨recoverBranch R.val A, recoverBranch_isCPTP A hA R⟩
  exact channelAverageInfidelity_eq_dim_ratio_fidelity L

#print axioms channelAverageInfidelity_eq_dim_ratio_fidelity
#print axioms channelAverageBranch_eq_dim_ratio_loss

end
end CriticalDepth.FaultAverageInfidelity
