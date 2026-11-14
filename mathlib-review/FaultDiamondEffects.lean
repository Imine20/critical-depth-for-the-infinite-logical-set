import FaultChannelEffects

/-!
Half diamond distance in operational form, with a finite reference of
arbitrary dimension and a positive two-outcome measurement effect.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.FaultCPTPRepresentation
open scoped BigOperators ComplexOrder Kronecker

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem amplify_trace (L : MatrixChannel ι ι) (hL : IsTracePreserving L)
    {Ref : Type*} [Fintype Ref] (X : Matrix (Ref × ι) (Ref × ι) ℂ) :
    (amplify L X).trace = X.trace := by
  simp only [Matrix.trace, Fintype.sum_prod_type, Matrix.diag_apply, amplify, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro r _
  exact hL (Matrix.of fun i j => X (r, i) (r, j))

theorem amplify_preserves_density (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L)
    (n : ℕ) {X : Matrix (Fin n × ι) (Fin n × ι) ℂ} (hX : IsDensity X) :
    IsDensity (amplify L X) :=
  ⟨hCP n X hX.1, (amplify_trace L hTP X).trans hX.2⟩

theorem amplify_id {Ref : Type*} (X : Matrix (Ref × ι) (Ref × ι) ℂ) :
    amplify (LinearMap.id : MatrixChannel ι ι) X = X := by
  ext p q
  rfl

theorem amplify_add {Ref : Type*} (L M : MatrixChannel ι ι)
    (X : Matrix (Ref × ι) (Ref × ι) ℂ) :
    amplify (L + M) X = amplify L X + amplify M X := by ext p q; rfl

theorem amplify_smul {Ref : Type*} (z : ℂ) (L : MatrixChannel ι ι)
    (X : Matrix (Ref × ι) (Ref × ι) ℂ) :
    amplify (z • L) X = z • amplify L X := by ext p q; rfl

/-- All unrestricted finite-reference tests distinguishing the channel from identity. -/
def channelEffectValues (L : MatrixChannel ι ι) : Set ℝ :=
  {p | ∃ (n : ℕ) (X E : Matrix (Fin n × ι) (Fin n × ι) ℂ),
    IsDensity X ∧ IsEffect E ∧ p = |effectValue E (amplify L X - X)|}

/-- Operational form of one half the completely bounded trace norm of L − id.
The trace-zero variational formula is the link to the trace-norm definition. -/
def halfDiamondByEffects (L : MatrixChannel ι ι) : ℝ :=
  sSup (channelEffectValues L)

theorem channelEffectValues_bdd (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L) :
    BddAbove (channelEffectValues L) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, X, E, hX, hE, rfl⟩
  exact effectValue_difference_abs_le_one hE (amplify_preserves_density L hCP hTP n hX) hX

theorem effect_test_le_halfDiamond (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L)
    (n : ℕ) (X E : Matrix (Fin n × ι) (Fin n × ι) ℂ)
    (hX : IsDensity X) (hE : IsEffect E) :
    |effectValue E (amplify L X - X)| ≤ halfDiamondByEffects L :=
  le_csSup (channelEffectValues_bdd L hCP hTP) ⟨n, X, E, hX, hE, rfl⟩

theorem halfDiamond_le_remainder_of_mixture (L M : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive M) (hTP : IsTracePreserving M)
    (r : ℝ) (hr : 0 ≤ r)
    (hL : L = ((1 - r : ℝ) : ℂ) • LinearMap.id + (r : ℂ) • M) :
    halfDiamondByEffects L ≤ r := by
  apply real_sSup_le_of_nonneg
  · rintro _ ⟨n, X, E, hX, hE, rfl⟩
    rw [hL, amplify_add, amplify_smul, amplify_smul, amplify_id]
    have hEq : (((1 - r : ℝ) : ℂ) • X + (r : ℂ) • amplify M X) - X =
        (r : ℂ) • (amplify M X - X) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rw [hEq, effectValue_smul, abs_mul, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr
      (effectValue_difference_abs_le_one hE (amplify_preserves_density M hCP hTP n hX) hX)
  · exact hr

#print axioms effect_test_le_halfDiamond
#print axioms halfDiamond_le_remainder_of_mixture

end

end CriticalDepth.FaultChannelEffects