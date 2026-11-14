import Q37NativeBlocks
import Q37ParityPolynomial

/-!
# From low-weight phase tests to all check coefficient sets

An affine shift by the logical word toggles the parity at precisely the
blocks where its own dot product is one. Evaluations use the finite
number of input rows, and the low-degree theorem extends the tests.
-/

open scoped BigOperators

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.FaultShorSaturation


/-- The coefficient positions where a block has odd pairing with its row. -/
def coefficientSupport (rows : List ℕ) (block : ℕ) : Finset (Fin rows.length) :=
  Finset.univ.filter fun i => dot block rows[i] = 1

/-- The integer sign from the affine logical shift in one block. -/
def affineBlockSign (logical block : ℕ) : ℤ :=
  if dot block logical = 1 then -1 else 1

/-- The finite tests imply the corresponding parity polynomial vanishes
on every coefficient mask, for either logical shift. -/
theorem phase_defect_of_small_tests (rows blocks : List ℕ) (logical : ℕ)
    (r : ℕ) (shift : Bool)
    (hsmall : ∀ S : Finset (Fin rows.length), S.card ≤ r →
      (∑ b : Fin blocks.length,
        ((if shift then affineBlockSign logical blocks[b] else 1) : ZMod (2 ^ r)) *
          (supportParity (coefficientSupport rows blocks[b]) S : ZMod (2 ^ r))) = 0) :
    ∀ S : Finset (Fin rows.length),
      (∑ b : Fin blocks.length,
        ((if shift then affineBlockSign logical blocks[b] else 1) : ZMod (2 ^ r)) *
          (supportParity (coefficientSupport rows blocks[b]) S : ZMod (2 ^ r))) = 0 := by
  classical
  let sign : Fin blocks.length → ℤ := fun b =>
    if shift then affineBlockSign logical blocks[b] else 1
  have hs := affineParitySum_of_small_masks Finset.univ
    (fun b : Fin blocks.length => coefficientSupport rows blocks[b]) sign r 0
    (fun S hS => by cases shift <;> simpa [sign] using hsmall S hS)
  cases shift <;> simpa [sign] using hs

/-- Pairing with a physical bit support equals a finite field dot product. -/
theorem dotProduct_wordOfNatMask (a b : ℕ) :
    dotProduct (wordOfNatMask 37 a) (wordOfNatMask 37 b) = ((dot a b : ℕ) : Bit) := by
  unfold dot
  rw [ZMod.natCast_mod]
  have hsum : dotProduct (wordOfNatMask 37 a) (wordOfNatMask 37 b) =
    ((∑ i : Fin 37, ((a &&& b).testBit i.val).toNat : ℕ) : Bit) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.testBit_land]
    cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;>
      simp [ha, hb, wordOfNatMask]
  exact hsum.trans (congrArg (fun k : ℕ => (k : Bit)) (weight_eq_sum_bits 37 (Nat.land a b)).symm)

#print axioms phase_defect_of_small_tests
#print axioms dotProduct_wordOfNatMask

end CriticalDepth.Q37BinaryData
