import FaultFirstBadOrder
import FaultHaarNativeModel
import FaultDiamondPaperMetric

/-! The first-failure result on the original gate-list experiment. -/

namespace CriticalDepth.FaultFirstBadOrder

open Filter Asymptotics
open CriticalDepth.Manuscript CriticalDepth.IndependentFaultHistories
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization
open CriticalDepth.FaultAverageInfidelity CriticalDepth.FaultChannelEffects
open scoped ENat Topology

noncomputable section

variable {n K q : ℕ} [Nonempty (Fin K × Fin 1)]

theorem paperCircuitErrorExponents_eq_firstUncorrectableOrder
    (C : Code n (fun _ => 2) K 1) (L : PaperLayers (n := n) (q := q))
    (μ : Law (PaperLabel L)) :
    let order := firstUncorrectableOrder (paperEncodedBranch C L)
    FaultExponent.exponent (paperCircuitInfidelity C L μ) = order ∧
    FaultExponent.exponent (paperCircuitAverageInfidelity C L μ) = order ∧
    FaultExponent.exponent (paperCircuitDiamond C L μ) = order :=
  historyErrorExponents_eq_firstUncorrectableOrder μ (paperEncodedBranch C L)
    (paperEncodedBranch_isometry C L)

/-- A finite entanglement-infidelity exponent gives an actual two-sided
bound for all three optimized errors on this same list and fault law. -/
theorem paperCircuitErrors_isTheta_of_exponent_eq
    (C : Code n (fun _ => 2) K 1) (L : PaperLayers (n := n) (q := q))
    (μ : Law (PaperLabel L)) (m : ℕ)
    (hm : FaultExponent.exponent (paperCircuitInfidelity C L μ) = (m : ℕ∞)) :
    (paperCircuitInfidelity C L μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
    (paperCircuitAverageInfidelity C L μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
    (paperCircuitDiamond C L μ =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) := by
  have hmOrder := (paperCircuitErrorExponents_eq_firstUncorrectableOrder C L μ).1.symm.trans hm
  rcases historyErrors_firstUncorrectableOrder μ (paperEncodedBranch C L)
      (paperEncodedBranch_isometry C L) with h | h
  · exact (ENat.coe_ne_top m (hmOrder.symm.trans h.1)).elim
  · obtain ⟨j, hj, _, _, hEnt, hAvg, hDia⟩ := h
    have hEq : j = m := by exact_mod_cast (hj.symm.trans hmOrder)
    subst j
    exact ⟨hEnt, hAvg, hDia⟩

/-- The same gate list can be used for any strictly positive weights. -/
theorem paperCircuitErrors_isTheta_of_exponent_eq_any_law
    (C : Code n (fun _ => 2) K 1) (L : PaperLayers (n := n) (q := q))
    (μ ν : Law (PaperLabel L)) (m : ℕ)
    (hm : FaultExponent.exponent (paperCircuitInfidelity C L μ) = (m : ℕ∞)) :
    (paperCircuitInfidelity C L ν =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
    (paperCircuitAverageInfidelity C L ν =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) ∧
    (paperCircuitDiamond C L ν =Θ[𝓝[>] (0 : ℝ)] fun p => p ^ m) := by
  apply paperCircuitErrors_isTheta_of_exponent_eq C L ν m
  exact (paperCircuitErrorExponents_eq_firstUncorrectableOrder C L ν).1.trans
    ((paperCircuitErrorExponents_eq_firstUncorrectableOrder C L μ).1.symm.trans hm)

theorem paperPerCodeDiamondExponent_eq_entanglement
    (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    paperPerCodeDiamondExponent C q h = paperPerCodeExponent C q h := by
  unfold paperPerCodeDiamondExponent paperPerCodeExponent FaultExponent.worstCaseExponent
  apply iInf_congr
  intro e
  have he := paperCircuitErrorExponents_eq_firstUncorrectableOrder C e.layers e.law
  exact he.2.2.trans he.1.symm

/-- A finite worst order is attained by an actual experiment in the infimum.
The gate list then attains that order for every positive Pauli law. -/
theorem exists_paperExperiment_at_finite_perCodeExponent
    (C : Code n (fun _ => 2) K 1) (q h m : ℕ)
    (hm : paperPerCodeExponent C q h = (m : ℕ∞)) :
    ∃ e : PaperExperiment C q h,
      FaultExponent.exponent (paperCircuitInfidelity C e.layers e.law) = (m : ℕ∞) := by
  let E (e : PaperExperiment C q h) := FaultExponent.exponent
    (paperCircuitInfidelity C e.layers e.law)
  change (⨅ e, E e) = (m : ℕ∞) at hm
  by_contra hNone
  have hNext (e : PaperExperiment C q h) : ((m + 1 : ℕ) : ℕ∞) ≤ E e := by
    have hLow : (m : ℕ∞) ≤ E e := hm.symm.le.trans (iInf_le E e)
    by_cases hTop : E e = ⊤
    · rw [hTop]
      exact le_top
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hTop
    have hj' : E e = (j : ℕ∞) := by first | exact hj | exact hj.symm
    rw [hj'] at hLow ⊢
    have hLow' : m ≤ j := by exact_mod_cast hLow
    have hn : j ≠ m := by
      intro he
      exact hNone ⟨e, hj'.trans (by rw [he])⟩
    exact_mod_cast (show m + 1 ≤ j by omega)
  have hlt := le_iInf hNext
  rw [hm] at hlt
  exact (Nat.not_succ_le_self m) (by exact_mod_cast hlt)

#print axioms paperCircuitErrorExponents_eq_firstUncorrectableOrder
#print axioms paperCircuitErrors_isTheta_of_exponent_eq_any_law
#print axioms paperPerCodeDiamondExponent_eq_entanglement
#print axioms exists_paperExperiment_at_finite_perCodeExponent

end
end CriticalDepth.FaultFirstBadOrder