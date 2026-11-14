import Q37SupportSplits
import Q37CheckSpaces

/-!
Correctness of the column signatures as simultaneous syndrome and logical parity.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.Manuscript20261114.CSSCheckSpaces

private theorem weight_eq_sum (n x : ℕ) :
    weight n x = ∑ i : Fin n, (x.testBit i.val).toNat :=
  weight_eq_sum_bits n x

theorem dot_nat_eq_binary (x y : ℕ) :
    (dot x y : Bit) = dotProduct (wordOfNatMask 37 x) (wordOfNatMask 37 y) := by
  unfold dot
  rw [weight_eq_sum]
  have hmod (k : ℕ) : ((k % 2 : ℕ) : Bit) = (k : Bit) := by
    apply ZMod.val_injective 2
    simp [ZMod.val_natCast, Nat.mod_mod]
  rw [hmod, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((Bool.toNat ((x &&& y).testBit i.val) : ℕ) : Bit) = _
  rw [Nat.testBit_land]
  cases hx : x.testBit i.val <;> cases hy : y.testBit i.val <;>
    simp [wordOfNatMask, hx, hy]

theorem dot_single_site_nat (a : ℕ) (i : Fin 37) :
    (dot a (1 <<< i.val) : Bit) = wordOfNatMask 37 a i := by
  rw [dot_nat_eq_binary]
  have he : wordOfNatMask 37 (1 <<< i.val) = Pi.single i 1 := by
    funext j
    rw [show wordOfNatMask 37 (1 <<< i.val) j =
      (if (1 <<< i.val).testBit j.val then 1 else 0 : Bit) from rfl]
    rw [Nat.shiftLeft_eq]
    simp only [one_mul]
    by_cases hj : j = i
    · subst j
      simp [Nat.testBit_two_pow]
    · have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp [Nat.testBit_two_pow, hne, Ne.symm hne, Pi.single_eq_of_ne hj]
  rw [he, dotProduct_single_one]

private def packBits : List ℕ → ℕ
  | [] => 0
  | b :: bs => b + 2 * packBits bs

private theorem packBits_eq_syndrome (checks : List ℕ) (x : ℕ) :
    syndrome checks x = packBits (checks.map fun c => dot c x) := by
  unfold syndrome
  have hfold (l : List ℕ) (offset acc : ℕ) :
      (l.zipIdx offset).foldl (fun r (c, i) => r + (dot c x <<< i)) acc =
        acc + 2 ^ offset * packBits (l.map fun c => dot c x) := by
    induction l generalizing offset acc with
    | nil => simp [packBits]
    | cons c cs ih =>
      simp only [List.zipIdx_cons, List.foldl_cons, List.map_cons, packBits]
      rw [ih, Nat.shiftLeft_eq]
      rw [pow_succ]
      ring
  rw [hfold, pow_zero, one_mul, zero_add]

private theorem testBit_packBits (bits : List ℕ) (hb : ∀ b ∈ bits, b < 2)
    (i : ℕ) :
    (packBits bits).testBit i = decide (bits[i]?.getD 0 = 1) := by
  induction bits generalizing i with
  | nil => simp [packBits]
  | cons b bs ih =>
    have hb0 := hb b (by simp)
    have hbs := fun x hx => hb x (List.mem_cons_of_mem b hx)
    have hbit : packBits (b :: bs) = Nat.bit (decide (b = 1)) (packBits bs) := by
      have he : b = 0 ∨ b = 1 := by omega
      rcases he with rfl | rfl <;> simp [packBits, Nat.bit, two_mul, add_comm, add_left_comm]
    rw [hbit]
    cases i with
    | zero => simp
    | succ i =>
        rw [Nat.testBit_bit_succ, ih hbs]
        rfl

theorem testBit_syndrome (checks : List ℕ) (x : ℕ) (i : ℕ) :
    (syndrome checks x).testBit i =
      decide ((checks[i]?.map (fun c => dot c x)).getD 0 = 1) := by
  rw [packBits_eq_syndrome, testBit_packBits]
  · simp
  · intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact Nat.mod_lt _ (by decide)

theorem signatureColumns_get (checks : List ℕ) (z : ℕ) (i : Fin 37) :
    (signatureColumns checks z)[i.val]'(by simpa [signatureColumns] using i.isLt) =
      2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val) := by
  simp [signatureColumns]

theorem signatureColumn_bit_zero (checks : List ℕ) (z : ℕ) (i : Fin 37) :
    (2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val)).testBit 0 =
      decide (dot z (1 <<< i.val) = 1) := by
  rw [Nat.testBit_zero]
  have hm : dot z (1 <<< i.val) < 2 := Nat.mod_lt _ (by decide)
  have he : (2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val)) % 2 =
      dot z (1 <<< i.val) := by omega
  simp [he]

theorem signatureColumn_bit_succ (checks : List ℕ) (z : ℕ) (i : Fin 37) (j : ℕ) :
    (2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val)).testBit (j + 1) =
      decide ((checks[j]?.map (fun c => dot c (1 <<< i.val))).getD 0 = 1) := by
  have h := Nat.testBit_div_two_pow
    (n := 1) (2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val)) j
  have hb : dot z (1 <<< i.val) < 2 := Nat.mod_lt _ (by decide)
  have he : (2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val)) / 2 ^ 1 =
      syndrome checks (1 <<< i.val) := by omega
  rw [he, testBit_syndrome] at h
  simpa [Nat.add_comm] using h.symm

end CriticalDepth.Q37BinaryData