import Q37DistanceData
import Q37ParityPolynomial

/-!
# Linking the finite Q37 check to subset evaluations

The certificate enumerator includes every choice of distinct input positions
with a given weight bound, even if the input columns have repeated values.
-/

namespace CriticalDepth.Q37BinaryData

/-- XOR the entries whose corresponding mask bits are set. -/
def maskedXor : List Bool → List Nat → Nat
  | bit :: bits, x :: xs =>
    if bit then Nat.xor x (maskedXor bits xs) else maskedXor bits xs
  | _, _ => 0

theorem maskedXor_mem_smallXorSums (bits : List Bool) (values : List Nat)
    (hsize : bits.length = values.length) (bound : ℕ)
    (hcount : (bits.filter id).length ≤ bound) :
    maskedXor bits values ∈ smallXorSums bound values := by
  induction values generalizing bits bound with
  | nil => simp [maskedXor, smallXorSums]
  | cons x xs ih =>
    cases bits with
    | nil => simp at hsize
    | cons b bits =>
      have hsize' : bits.length = xs.length := by simpa using hsize
      cases bound with
      | zero =>
        have hzero (bits : List Bool) (values : List Nat)
            (hc : (bits.filter id).length = 0) : maskedXor bits values = 0 := by
          induction bits generalizing values with
          | nil => cases values <;> rfl
          | cons bit bits ih =>
            cases values with
            | nil => rfl
            | cons y ys =>
              cases bit
              · exact ih ys (by simpa using hc)
              · simp at hc
        have hzero' := hzero (b :: bits) (x :: xs) (Nat.eq_zero_of_le_zero hcount)
        rw [hzero']
        simp [smallXorSums]
      | succ bound =>
        cases b
        · simp only [maskedXor, Bool.false_eq_true, ite_false, smallXorSums]
          exact List.mem_append_left _ (ih bits hsize' (bound + 1) (by simpa using hcount))
        · simp only [maskedXor, ite_true, smallXorSums]
          apply List.mem_append_right
          apply List.mem_map.mpr
          refine ⟨maskedXor bits xs, ih bits hsize' bound ?_, rfl⟩
          simpa using hcount

theorem certificate_agrees_on_masked_halves {columns : List Nat}
    (certificate : (List.range 8).all (parityConsistentBucket columns) = true)
    (bits bits' : List Bool) (hbits : bits.length = columns.length)
    (hbits' : bits'.length = columns.length)
    (hw : (bits.filter id).length ≤ 3) (hw' : (bits'.filter id).length ≤ 3)
    (hs : maskedXor bits columns / 2 = maskedXor bits' columns / 2)
    (hb : maskedXor bits columns / 2 < 2 ^ 18) :
    maskedXor bits columns % 2 = maskedXor bits' columns % 2 := by
  apply parityConsistent_of_bucket_certificates certificate
    (a := (maskedXor bits columns / 2, maskedXor bits columns % 2))
    (b := (maskedXor bits' columns / 2, maskedXor bits' columns % 2))
  · exact List.mem_map.mpr ⟨_, maskedXor_mem_smallXorSums bits columns hbits 3 hw, rfl⟩
  · exact List.mem_map.mpr ⟨_, maskedXor_mem_smallXorSums bits' columns hbits' 3 hw', rfl⟩
  · exact hb
  · exact hs

#print axioms maskedXor_mem_smallXorSums
#print axioms certificate_agrees_on_masked_halves

end CriticalDepth.Q37BinaryData