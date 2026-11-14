import FaultLocalStochasticRecovery
import FaultHistoryExperimentNormalization

/-!
The local-stochastic bound on the paper's original finite lists of gates,
with all probabilities and joint events on that carrier.
-/

namespace CriticalDepth.FaultChannelEffects

noncomputable section

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultDepthArithmetic
open CriticalDepth.IndependentFaultHistories CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization

variable {n K q : ℕ} [Nonempty (Fin K × Fin 1)]

/-- The binomial order is computed from the advertised depth budget. The common
recovery corrects histories below that order on the original gate-list carrier. -/
theorem paper_localStochastic_recovery_bounds_at_depth
    (C : Code n (fun _ => 2) K 1) (d : ℕ) (hdetect : DetectsBelow C d)
    (L : PaperLayers (n := n) (q := q)) (h : ℕ) (hDepth : L.length ≤ h)
    (hq : 1 ≤ q) (W : Operator (Fin K))
    (hW : Implements C (paperSequenceEval L) W) (p : ℝ)
    (μ : LocalStochasticMass (Finset.univ : Finset (PaperLocation L))
      (faults (Label := PaperLabel L)) p) :
    let bound := ((Fintype.card (PaperLocation L)).choose (lowerEnvelope q d h) : ℝ) *
      p ^ lowerEnvelope q d h
    optimalMassEntanglementInfidelity μ.weight (paperEncodedBranch C L) ≤ bound ∧
      optimalMassHalfDiamond μ.weight (paperEncodedBranch C L) ≤ bound := by
  have hW' : Implements C (layerSequenceEval (normalizedLayers L)) W :=
    implements_of_projectivelyEquivalent_physical C (sequence_normalization_phase L) hW
  have hlen : (normalizedLayers L).length = L.length := by simp [normalizedLayers]
  have hden : q ^ L.length + q ≤ q ^ h + q :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) hDepth) q
  have hActualPos : 0 < q ^ L.length + q := by omega
  have hBudgetPos : 0 < q ^ h + q := by omega
  have hActual : d ≤ lowerEnvelope q d L.length * (q ^ L.length + q) :=
    (ceilDiv_le_iff d _ (lowerEnvelope q d L.length) hActualPos).mp le_rfl
  have hOrder : lowerEnvelope q d h ≤ lowerEnvelope q d L.length :=
    (ceilDiv_le_iff d _ (lowerEnvelope q d L.length) hBudgetPos).mpr
      (hActual.trans (Nat.mul_le_mul_left _ hden))
  have hA (x : History (PaperLabel L)) :
      (paperEncodedBranch C L x).conjTranspose * paperEncodedBranch C L x = 1 := by
    rw [paperEncodedBranch_eq_native]
    exact encodedBranch_isometry C _
  have hscalar (x y : History (PaperLabel L))
      (hx : (faults x).card < lowerEnvelope q d h)
      (hy : (faults y).card < lowerEnvelope q d h) :
      ∃ z : ℂ, (paperEncodedBranch C L x).conjTranspose * paperEncodedBranch C L y =
        z • (1 : Matrix (Fin K × Fin 1) (Fin K × Fin 1) ℂ) := by
    simp only [paperEncodedBranch_eq_native]
    apply native_low_fault_scalarCrossTerms C d hdetect (normalizedLayers L) hq W hW'
    · rw [historyEquiv_fault_count, hlen]
      exact hx.trans_le hOrder
    · rw [historyEquiv_fault_count, hlen]
      exact hy.trans_le hOrder
  simpa only [Finset.card_univ] using
    localStochastic_recovery_bounds Finset.univ faults p μ (paperEncodedBranch C L)
      hA (lowerEnvelope q d h) hscalar

theorem paper_localStochastic_recovery_bounds
    (C : Code n (fun _ => 2) K 1) (d : ℕ) (hdetect : DetectsBelow C d)
    (L : PaperLayers (n := n) (q := q)) (hq : 1 ≤ q) (W : Operator (Fin K))
    (hW : Implements C (paperSequenceEval L) W) (p : ℝ)
    (μ : LocalStochasticMass (Finset.univ : Finset (PaperLocation L))
      (faults (Label := PaperLabel L)) p) :
    let bound := ((Fintype.card (PaperLocation L)).choose (lowerEnvelope q d L.length) : ℝ) *
      p ^ lowerEnvelope q d L.length
    optimalMassEntanglementInfidelity μ.weight (paperEncodedBranch C L) ≤ bound ∧
      optimalMassHalfDiamond μ.weight (paperEncodedBranch C L) ≤ bound :=
  paper_localStochastic_recovery_bounds_at_depth C d hdetect L L.length le_rfl hq W hW p μ

#print axioms paper_localStochastic_recovery_bounds_at_depth
#print axioms paper_localStochastic_recovery_bounds

end
end CriticalDepth.FaultChannelEffects
