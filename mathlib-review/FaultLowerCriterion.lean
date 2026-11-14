import FaultNativeCeiling

/-!
# Sharpness from two native histories

This criterion packages the remaining physical witness for lower saturation.
The assumptions refer to the same noisy experiment and its encoded branches.
-/

namespace CriticalDepth.FaultNativeModel

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.IndependentFaultHistories CriticalDepth.EncodedFaultRecovery
open CriticalDepth.FaultDepthArithmetic
open scoped ENat

theorem perCodeExponent_eq_lower_of_ambiguous
    {n K q d h : ℕ} [Nonempty (Fin K × Fin 1)]
    (C : Code n (fun _ => 2) K 1) (hq : 1 ≤ q) (hd : DetectsBelow C d)
    (e : Experiment C q h)
    (x y : History (fun i : Location e.layers => FaultLabel i)) (hxy : x ≠ y)
    (W : Operator (Fin K × Fin 1)) (hW : W * W.conjTranspose = 1)
    (htr : Matrix.trace W = 0)
    (hbranch : encodedBranch C y = encodedBranch C x * W)
    (hx : (faults x).card ≤ lowerEnvelope q d h)
    (hy : (faults y).card ≤ lowerEnvelope q d h) :
    perCodeExponent C q h = (lowerEnvelope q d h : ℕ∞) := by
  refine le_antisymm ?_ (perCodeExponent_floor C q d h hq hd)
  refine (iInf_le _ e).trans ?_
  have hamb := ambiguous_exponent_of_traceless_unitary e.law (encodedBranch C)
    (encodedBranch_isometry C) x y hxy W hW htr hbranch
  exact hamb.trans (by exact_mod_cast max_le hx hy)

#print axioms perCodeExponent_eq_lower_of_ambiguous

end CriticalDepth.FaultNativeModel