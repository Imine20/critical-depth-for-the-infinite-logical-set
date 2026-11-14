import FaultVariationalTrace
import FaultDiamondEffects

/-!
On differences of channel outputs, the operational definition equals the
unrestricted stabilized trace distance on density inputs.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.FaultCPTPRepresentation
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem densityDifference_hermitian {n : ℕ} (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (X : Matrix (Fin n × ι) (Fin n × ι) ℂ)
    (hX : IsDensity X) : (amplify L X - X).IsHermitian :=
  (hCP n X hX.1).1.sub hX.1.1

theorem densityDifference_trace_zero {n : ℕ} (L : MatrixChannel ι ι)
    (hTP : IsTracePreserving L) (X : Matrix (Fin n × ι) (Fin n × ι) ℂ) :
    (amplify L X - X).trace = 0 := by
  rw [Matrix.trace_sub, amplify_trace L hTP X, sub_self]

def channelStateTraceValues (L : MatrixChannel ι ι) (hCP : IsCompletelyPositive L) : Set ℝ :=
  {p | ∃ (n : ℕ) (X : Matrix (Fin n × ι) (Fin n × ι) ℂ) (hX : IsDensity X),
    p = hermitianTraceNorm (amplify L X - X) (densityDifference_hermitian L hCP X hX) / 2}

theorem halfDiamondByEffects_eq_halfStabilizedTraceDistance
    (L : MatrixChannel ι ι) (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L) :
    halfDiamondByEffects L = sSup (channelStateTraceValues L hCP) := by
  have span (n : ℕ) (X : Matrix (Fin n × ι) (Fin n × ι) ℂ) (hX : IsDensity X) :=
    effect_diagonal_spectral_bound (densityDifference_hermitian L hCP X hX)
      (densityDifference_trace_zero L hTP X)
  have hsub : channelStateTraceValues L hCP ⊆ channelEffectValues L := by
    rintro p ⟨n, X, hX, rfl⟩
    obtain ⟨E, hE, he⟩ := (span n X hX).1
    exact ⟨n, X, E, hX, hE, he⟩
  have hB := channelEffectValues_bdd L hCP hTP
  have hState : BddAbove (channelStateTraceValues L hCP) := hB.mono hsub
  apply le_antisymm
  · unfold halfDiamondByEffects
    apply real_sSup_le_of_nonneg
    · rintro _ ⟨n, X, E, hX, hE, rfl⟩
      exact ((span n X hX).2 ⟨E, hE, rfl⟩).trans
        (le_csSup hState ⟨n, X, hX, rfl⟩)
    · exact Real.sSup_nonneg (by
        rintro _ ⟨n, X, hX, rfl⟩
        exact div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by norm_num))
  · unfold halfDiamondByEffects
    apply real_sSup_le_of_nonneg
    · intro a ha
      exact le_csSup hB (hsub ha)
    · exact Real.sSup_nonneg (by
        rintro _ ⟨n, X, E, hX, hE, rfl⟩
        exact abs_nonneg _)

#print axioms halfDiamondByEffects_eq_halfStabilizedTraceDistance

end

end CriticalDepth.FaultChannelEffects