import CSSUpperSaturation
import CSSRandomRigidity
import FaultHistoryExperimentNormalization

/-!
Unconditional sharpness of the upper fault envelope on the CSS family
for all sufficiently large depths, with one code for every allowed depth.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript
open CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryExperimentNormalization
open scoped Matrix BigOperators ENat

theorem exists_css_check_matrix {n : ℕ} (J : Submodule CSSBit (CSSWord n)) :
    ∃ B : Matrix (Fin (Module.finrank CSSBit J)) (Fin n) CSSBit,
      Function.Injective (fun a : Fin (Module.finrank CSSBit J) → CSSBit => a ᵥ* B) ∧
      ∀ w : CSSWord n, w ∈ J ↔ ∃ a : Fin (Module.finrank CSSBit J) → CSSBit, a ᵥ* B = w := by
  classical
  let E := Module.finBasis CSSBit J
  let B : Matrix (Fin (Module.finrank CSSBit J)) (Fin n) CSSBit := fun i j => (E i).val j
  have hB (a : Fin (Module.finrank CSSBit J) → CSSBit) : a ᵥ* B = (E.equivFun.symm a).val := by
    funext j
    have h := congrArg (fun x : J => x.val j) (E.equivFun_symm_apply a)
    simpa [B, Matrix.vecMul, dotProduct, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      using h.symm
  refine ⟨B, ?_, ?_⟩
  · intro a a' he
    change a ᵥ* B = a' ᵥ* B at he
    apply E.equivFun.symm.injective
    apply Subtype.ext
    rwa [hB, hB] at he
  · intro w
    constructor
    · intro hw
      refine ⟨E.equivFun ⟨w, hw⟩, ?_⟩
      rw [hB, LinearEquiv.symm_apply_apply]
    · rintro ⟨a, rfl⟩
      rw [hB]
      exact (E.equivFun.symm a).property

theorem exists_css_upper_saturation (q t : ℕ) (hq : 2 ≤ q) (ht : 20 ≤ t) :
    let R := q ^ t
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (hc : H ≤ cssOrthogonal J),
      let C := physicalCSSCode H J hc
      IsStabilizer C ∧ HasActualDistance C (cssDistance R) ∧
      cssLogicalQubits H J = cssSites R - cssXDimension R - cssZDimension R ∧
      ∀ h, 1 ≤ h → h ≤ t →
        perCodeExponent C q h = (upperEnvelope q (cssDistance R) h : ℕ∞) ∧
        paperPerCodeExponent C q h = (upperEnvelope q (cssDistance R) h : ℕ∞) := by
  let R := q ^ t
  have hR : 2 ^ 20 ≤ R := (Nat.pow_le_pow_right (by decide) ht).trans (Nat.pow_le_pow_left hq t)
  obtain ⟨H, J, p, S, hH, hJ, hp, hpd, hDual⟩ := exists_rigid_checkSpaces R hR
  obtain ⟨B, hRows, hB⟩ := exists_css_check_matrix J
  have hd : 2 ≤ cssDistance R := by
    have hR2 : 2 ≤ R := (by decide : 2 ≤ 2 ^ 20).trans hR
    unfold cssDistance
    nlinarith
  have hp₀ : p ≠ 0 := by
    rintro rfl
    simp [wordWeight] at hpd
    omega
  have hpJ : p ∉ J := by
    intro h
    have hDist := S.zDistance p h hp₀
    rw [hH, hJ, hpd] at hDist
    exact (not_lt_of_ge (cssDistance_le_deletionThreshold R (by omega))) hDist
  have hdR : cssDistance R ≤ q ^ t * (Module.finrank CSSBit H + 1) := by
    rw [hH]
    exact cssDistance_le_supportBound R (by omega)
  have h := physicalCSS_attains_upperEnvelope hq hd H J S p hp hpJ hpd hDual hdR B hRows hB
  refine ⟨H, J, S.compatible, physicalCSSCode_isStabilizer H J S.compatible, h.1, ?_, ?_⟩
  · rw [cssLogicalQubits_eq_sub H J S.compatible, hH, hJ]
  · intro ell he he'
    have hn := h.2 ell he he'
    exact ⟨hn, (paperPerCodeExponent_eq_native _ _ _).trans hn⟩

#print axioms exists_css_upper_saturation

end CriticalDepth.Manuscript20261114.CSSCheckSpaces