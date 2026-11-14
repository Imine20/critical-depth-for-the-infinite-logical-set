import CSSCircuitRigidity
import CSSCodeDimension
import CSSCodeDistance

/-!
# Fault exponent on a CSS code with the manuscript's check spaces
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript CriticalDepth.Arithmetic
open CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultSupportPreserving
open scoped ENat Matrix

theorem physicalCSS_attains_upperEnvelope {n q t d : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d)
    (H J : Submodule CSSBit (CSSWord n))
    (S : RigidityCheckSpaces H J (q ^ t))
    (z : CSSWord n) (hz : z ∈ cssOrthogonal H) (hzJ : z ∉ J) (hweight : wordWeight z = d)
    (hAllZ : ∀ w ∈ cssOrthogonal H, w ≠ 0 → d ≤ wordWeight w)
    (hdR : d ≤ q ^ t * (Module.finrank CSSBit H + 1))
    (B : Matrix (Fin (Module.finrank CSSBit J)) (Fin n) CSSBit)
    (hRows : Function.Injective (fun a : Fin (Module.finrank CSSBit J) → CSSBit => a ᵥ* B))
    (hB : ∀ w : CSSWord n, w ∈ J ↔ ∃ a : Fin (Module.finrank CSSBit J) → CSSBit, a ᵥ* B = w) :
    let C := physicalCSSCode H J S.compatible
    HasActualDistance C d ∧ ∀ h, 1 ≤ h → h ≤ t →
      perCodeExponent C q h = (upperEnvelope q d h : ℕ∞) := by
  let C := physicalCSSCode H J S.compatible
  have hdist : HasActualDistance C d :=
    physicalCSSCode_hasActualDistance H J S.compatible hAllZ
      (fun w hw hn => hdR.trans (S.zDualDistance w hw hn).le) z hz hzJ hweight
  refine ⟨hdist, ?_⟩
  intro h hh hht
  apply perCodeExponent_eq_upper_of_preservesSupports C
    (physicalCSSCode_isStabilizer H J S.compatible) hdist hd hq hh
  intro e
  have hpow : q ^ e.layers.length ≤ q ^ t :=
    Nat.pow_le_pow_right (by omega) (e.depth.trans hht)
  exact physicalCSS_exactCircuit_preservesSupports H J q (q ^ t) (by omega)
    (show 0 < q ^ t from pow_pos (by omega : 0 < q) t) S B hRows hB e.layers hpow e.logical e.exactAction

#print axioms physicalCSS_attains_upperEnvelope

end CriticalDepth.Manuscript20261114.CSSCheckSpaces