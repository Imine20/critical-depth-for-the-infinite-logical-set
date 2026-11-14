import FaultNativeCeiling

/-!
# Depth-one saturation

At depth one the two exponent envelopes coincide. This proves saturation
for every stabilizer code of the specified distance in the native model.
-/

namespace CriticalDepth.FaultNativeCeiling

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open scoped ENat

theorem upperEnvelope_one_eq_lower (q d : ℕ) :
    upperEnvelope q d 1 = lowerEnvelope q d 1 := by
  simp [upperEnvelope, lowerEnvelope, ceilHalf, two_mul]

theorem perCodeExponent_depth_one_eq {n k d q : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstab : IsStabilizer C) (hdist : HasActualDistance C d)
    (hd : 2 ≤ d) (hq : 2 ≤ q) :
    perCodeExponent C q 1 = (ceilDiv d (2 * q) : ℕ∞) := by
  obtain ⟨hfloor, hceil⟩ :=
    stabilizer_perCodeExponent_envelopes (h := 1) C hstab hdist hd hq le_rfl
  rw [upperEnvelope_one_eq_lower] at hceil
  simpa [lowerEnvelope, two_mul] using le_antisymm hceil hfloor

#print axioms upperEnvelope_one_eq_lower
#print axioms perCodeExponent_depth_one_eq

end CriticalDepth.FaultNativeCeiling