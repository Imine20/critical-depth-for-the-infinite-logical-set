import FaultDiamondHistories
import FaultHistoryExperimentNormalization

/-! Relabeling unobserved histories preserves their recovered mixture. -/

namespace CriticalDepth.FaultChannelEffects

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultCPTPRepresentation
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization
open scoped BigOperators

noncomputable section
variable {n K q : ℕ} [Nonempty (Fin K × Fin 1)]

theorem paperRecoveredHistoryChannel_eq_native (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L))
    (p : ℝ) (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) :
    recoveredHistoryChannel μ (paperEncodedBranch C L) p R =
      recoveredHistoryChannel (pushLaw L μ) (encodedBranch C) p R := by
  let V := fun y : History (fun i : Location (normalizedLayers L) => FaultLabel i) =>
    (mass (pushLaw L μ) p y : ℂ) • recoverBranch R.val (encodedBranch C y)
  let U := fun x : History (PaperLabel L) =>
    (mass μ p x : ℂ) • recoverBranch R.val (paperEncodedBranch C L x)
  change ∑ x, U x = ∑ y, V y
  have h (x : History (PaperLabel L)) : U x = V (historyEquiv L x) := by
    have hm := historyEquiv_mass L (pushLaw L μ) p x
    rw [pull_push_history_law] at hm
    change (mass μ p x : ℂ) • recoverBranch R.val (paperEncodedBranch C L x) =
      (mass (pushLaw L μ) p (historyEquiv L x) : ℂ) •
        recoverBranch R.val (encodedBranch C (historyEquiv L x))
    rw [hm, paperEncodedBranch_eq_native]
  calc
    _ = ∑ x, V (historyEquiv L x) := Finset.sum_congr rfl (fun x _ => h x)
    _ = _ := (historyEquiv L).sum_comp V

theorem nativeRecoveredHistoryChannel_eq_paper (C : Code n (fun _ => 2) K 1)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i))
    (p : ℝ) (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) :
    recoveredHistoryChannel μ (encodedBranch C) p R =
      recoveredHistoryChannel (reverseLaw L μ) (paperEncodedBranch C (paperLayersOfNative L)) p R := by
  let V := fun y : History (PaperLabel (paperLayersOfNative L)) =>
    (mass (reverseLaw L μ) p y : ℂ) • recoverBranch R.val
      (paperEncodedBranch C (paperLayersOfNative L) y)
  let U := fun x : History (fun i : Location L => FaultLabel i) =>
    (mass μ p x : ℂ) • recoverBranch R.val (encodedBranch C x)
  change ∑ x, U x = ∑ y, V y
  have h (x : History (fun i : Location L => FaultLabel i)) :
      U x = V (reverseHistoryEquiv L x) := by
    change (mass μ p x : ℂ) • recoverBranch R.val (encodedBranch C x) =
      (mass (reverseLaw L μ) p (reverseHistoryEquiv L x) : ℂ) • recoverBranch R.val
        (paperEncodedBranch C (paperLayersOfNative L) (reverseHistoryEquiv L x))
    rw [reverseHistoryEquiv_mass, paperEncodedBranch_eq_reverse]
  calc
    _ = ∑ x, V (reverseHistoryEquiv L x) := Finset.sum_congr rfl (fun x _ => h x)
    _ = _ := (reverseHistoryEquiv L).sum_comp V

#print axioms paperRecoveredHistoryChannel_eq_native
#print axioms nativeRecoveredHistoryChannel_eq_paper

end
end CriticalDepth.FaultChannelEffects
