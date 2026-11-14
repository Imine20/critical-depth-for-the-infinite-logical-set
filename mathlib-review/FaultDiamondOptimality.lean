import FaultDiamondHistories
import FaultKrausCompactness
import Mathlib.Topology.Semicontinuity.Basic

/-!
The operational diamond error attains a minimum over terminal CPTP recovery.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.FaultCPTPRepresentation CriticalDepth.FaultCPTPOptimality
open CriticalDepth.FaultKrausCompactness CriticalDepth.IndependentFaultHistories
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {Phys Log Loc : Type*} [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

private structure StateEffectTest (ι : Type*) [Fintype ι] [DecidableEq ι] where
  size : ℕ
  state : Matrix (Fin size × ι) (Fin size × ι) ℂ
  effect : Matrix (Fin size × ι) (Fin size × ι) ℂ
  isState : IsDensity state
  isEffect : IsEffect effect

private def testValue (L : MatrixChannel Log Log) (t : StateEffectTest Log) : ℝ :=
  |effectValue t.effect (amplify L t.state - t.state)|

private theorem channelEffectValues_range (L : MatrixChannel Log Log) :
    channelEffectValues L = Set.range (testValue L) := by
  ext x
  constructor
  · rintro ⟨n, X, E, hX, hE, rfl⟩
    exact ⟨⟨n, X, E, hX, hE⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t.size, t.state, t.effect, t.isState, t.isEffect, rfl⟩

private def recoveredKrausHistory (μ : Law Label) (A : History Label → Matrix Phys Log ℂ) (p : ℝ)
    (K : (Phys × Log) → Matrix Log Phys ℂ) : MatrixChannel Log Log :=
  ∑ x, (mass μ p x : ℂ) • recoverBranch (krausMap K) (A x)

private theorem recoveredKrausHistory_continuous_test (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (p : ℝ) (t : StateEffectTest Log) :
    Continuous (fun K => testValue (recoveredKrausHistory μ A p K) t) := by
  apply Continuous.abs
  change Continuous (fun K => ((t.effect * (amplify (recoveredKrausHistory μ A p K)
    t.state - t.state)).trace).re)
  apply Complex.continuous_re.comp
  unfold Matrix.trace
  apply continuous_finsetSum
  intro u _
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.sub_apply]
  apply continuous_finsetSum
  intro v _
  apply continuous_const.mul
  apply Continuous.sub _ continuous_const
  simp only [amplify, Matrix.of_apply, recoveredKrausHistory, LinearMap.sum_apply,
    LinearMap.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro x _
  apply continuous_const.mul
  change Continuous (fun K => krausMap K (A x *
    (Matrix.of fun i j => t.state (v.1, i) (u.1, j)) * (A x).conjTranspose) v.2 u.2)
  simp only [krausMap_apply, Matrix.sum_apply]
  apply continuous_finsetSum
  intro k _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply continuous_finsetSum
  intro i _
  have hEntry (a : Log) (b : Phys) :
      Continuous (fun K : (Phys × Log) → Matrix Log Phys ℂ => K k a b) := by
    have hK : Continuous (fun K : (Phys × Log) → Matrix Log Phys ℂ => K k) :=
      continuous_apply k
    have hRow : Continuous (fun K : (Phys × Log) → Matrix Log Phys ℂ => K k a) :=
      (continuous_apply a).comp hK
    exact (continuous_apply b).comp hRow
  apply Continuous.mul
  · apply continuous_finsetSum
    intro j _
    exact (hEntry v.2 j).mul continuous_const
  · exact (hEntry u.2 i).star

theorem exists_cptp_optimalHistoryDiamond (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    ∃ R : RecoveryChannel Phys Log,
      halfDiamondByEffects (recoveredHistoryChannel μ A p R) = optimalHistoryDiamond μ A p := by
  let S := tpFamilies (Phys := Phys) (Log := Log) (Rec := Phys × Log)
  let recovery (K : (Phys × Log) → Matrix Log Phys ℂ) (hK : K ∈ S) :
      RecoveryChannel Phys Log :=
    ⟨krausMap K, kraus_isCompletelyPositive K, (kraus_isTracePreserving_iff K).mpr hK⟩
  have hsurj (R : RecoveryChannel Phys Log) : ∃ K, ∃ hK : K ∈ S, recovery K hK = R := by
    obtain ⟨K, hEq, hTP⟩ := (cptp_iff_exists_completeKraus R.val).mp R.property
    exact ⟨K, hTP, Subtype.ext hEq.symm⟩
  have hne : S.Nonempty := by
    obtain ⟨R, _⟩ := exists_cptp_optimalInfidelity μ A p
    obtain ⟨K, hK, _⟩ := hsurj R
    exact ⟨K, hK⟩
  have hcont : LowerSemicontinuousOn (fun K =>
      halfDiamondByEffects (recoveredKrausHistory μ A p K)) S := by
    simp only [halfDiamondByEffects, channelEffectValues_range, sSup_range]
    apply lowerSemicontinuousOn_ciSup
    · intro K hK
      rw [← channelEffectValues_range]
      have hc := historyChannel_isCPTP μ A hA p hp hp₁ (recovery K hK)
      exact channelEffectValues_bdd _ hc.1 hc.2
    · intro t
      exact (recoveredKrausHistory_continuous_test μ A p t).continuousOn.lowerSemicontinuousOn
  obtain ⟨K, hK, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne isCompact_tpFamilies hcont
  let R₀ := recovery K hK
  have hle : ∀ R : RecoveryChannel Phys Log,
      halfDiamondByEffects (recoveredHistoryChannel μ A p R₀) ≤
        halfDiamondByEffects (recoveredHistoryChannel μ A p R) := by
    intro R
    obtain ⟨T, hT, rfl⟩ := hsurj R
    exact (isMinOn_iff.mp hmin) T hT
  refine ⟨R₀, ?_⟩
  let f := fun R : RecoveryChannel Phys Log => halfDiamondByEffects (recoveredHistoryChannel μ A p R)
  have hb : f R₀ ∈ lowerBounds (Set.range f) := by
    rintro _ ⟨R, rfl⟩
    exact hle R
  exact le_antisymm (le_csInf ⟨_, Set.mem_range_self R₀⟩ hb)
    (csInf_le ⟨_, hb⟩ (Set.mem_range_self R₀))

#print axioms exists_cptp_optimalHistoryDiamond

end
end CriticalDepth.FaultChannelEffects
