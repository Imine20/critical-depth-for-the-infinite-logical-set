import ShorStabilizer
import ShorExactDistance
import FaultDepthOne
import FaultLowerCriterion

/-!
# Lower saturation on rectangular Shor codes

The rectangular code is defined on the original qubit register. These
consequences of the native fault bounds isolate the multi-layer circuit
witness from the proof of its distance and stabilizer properties.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultNativeCeiling CriticalDepth.IndependentFaultHistories
open scoped ENat

theorem physicalShorCode_saturates_at_depth_one {rows columns q : ℕ}
    (i : Fin rows) (hside : columns + 1 ≤ rows) (hd : 2 ≤ columns + 1) (hq : 2 ≤ q) :
    perCodeExponent (physicalShorCode (columns := columns) i) q 1 =
      (lowerEnvelope q (columns + 1) 1 : ℕ∞) := by
  have h := perCodeExponent_depth_one_eq
    (physicalShorCode (columns := columns) i)
    (physicalShorCode_isStabilizer i)
    (physicalShorCode_hasActualDistance i hside) hd hq
  simpa [lowerEnvelope, two_mul] using h

theorem physicalShorCode_saturates_of_native_histories {rows columns q h : ℕ}
    (i : Fin rows) (hside : columns + 1 ≤ rows) (hq : 1 ≤ q)
    (e : Experiment (physicalShorCode (columns := columns) i) q h)
    (x y : History (fun j : Location e.layers => FaultLabel j)) (hxy : x ≠ y)
    (W : Operator (Fin 2 × Fin 1)) (hW : W * W.conjTranspose = 1) (htr : Matrix.trace W = 0)
    (hbranch : encodedBranch (physicalShorCode (columns := columns) i) y =
      encodedBranch (physicalShorCode (columns := columns) i) x * W)
    (hx : (faults x).card ≤ lowerEnvelope q (columns + 1) h)
    (hy : (faults y).card ≤ lowerEnvelope q (columns + 1) h) :
    perCodeExponent (physicalShorCode (columns := columns) i) q h =
      (lowerEnvelope q (columns + 1) h : ℕ∞) :=
  perCodeExponent_eq_lower_of_ambiguous _ hq (physicalShorCode_hasActualDistance i hside).1
    e x y hxy W hW htr hbranch hx hy

#print axioms physicalShorCode_saturates_at_depth_one
#print axioms physicalShorCode_saturates_of_native_histories


/-- The advertised depth-one member of the rectangular family, with exactly
ceil(d/(2q)) · 2q rows. -/
theorem exists_depth_one_lower_saturation (d q : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q) :
    ∃ C : Code (lowerEnvelope q d 1 * (q ^ 1 + q) * d) (fun _ => 2) (2 ^ 1) 1,
      IsStabilizer C ∧ HasActualDistance C d ∧
        perCodeExponent C q 1 = (lowerEnvelope q d 1 : ℕ∞) := by
  obtain ⟨columns, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  let rows := lowerEnvelope q (columns + 1) 1 * (q ^ 1 + q)
  have hside : columns + 1 ≤ rows :=
    (ceilDiv_le_iff _ _ _ (by omega)).mp le_rfl
  let i : Fin rows := ⟨0, by omega⟩
  exact ⟨physicalShorCode (columns := columns) i, physicalShorCode_isStabilizer i,
    physicalShorCode_hasActualDistance i hside,
    physicalShorCode_saturates_at_depth_one i hside hd hq⟩

#print axioms exists_depth_one_lower_saturation
end CriticalDepth.FaultShorSaturation