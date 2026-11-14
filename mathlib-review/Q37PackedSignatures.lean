import Q37SignatureBits

/-!
The half-signature check proves vanishing logical pairing for a quiet word
of weight at most six.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.Manuscript20261114.CSSCheckSpaces

def maskWord (S : Finset (Fin 37)) : Q37Word := fun i => if i ∈ S then 1 else 0

def halfSignature (columns : List ℕ) (S : Finset (Fin 37)) : ℕ :=
  maskedXor (List.ofFn fun i : Fin 37 => decide (i ∈ S)) columns

theorem signatureColumns_list (checks : List ℕ) (z : ℕ) :
    signatureColumns checks z =
      List.ofFn (fun i : Fin 37 => 2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val)) := by
  apply List.ext_getElem
  · simp [signatureColumns]
  · intro i h₁ h₂
    have hi : i < 37 := by simpa using h₂
    simpa only [List.getElem_ofFn] using signatureColumns_get checks z ⟨i, hi⟩

private theorem if_bit_dot_eq (x y : ℕ) :
    (if dot x y = 1 then (1 : Bit) else 0) = (dot x y : Bit) := by
  have h : dot x y < 2 := Nat.mod_lt _ (by decide)
  have he : dot x y = 0 ∨ dot x y = 1 := by omega
  rcases he with ho | ho <;> simp [ho]

theorem halfSignature_bit_zero (checks : List ℕ) (z : ℕ) (S : Finset (Fin 37)) :
    (if (halfSignature (signatureColumns checks z) S).testBit 0 then (1 : Bit) else 0) =
      dotProduct (wordOfNatMask 37 z) (maskWord S) := by
  unfold halfSignature
  rw [signatureColumns_list, maskedXor_eval_bit, dotProduct_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [signatureColumn_bit_zero]
  simp only [decide_eq_true_eq, if_bit_dot_eq, dot_single_site_nat, maskWord, dotProduct]

theorem halfSignature_bit_succ (checks : List ℕ) (z : ℕ)
    (S : Finset (Fin 37)) (j : Fin checks.length) :
    (if (halfSignature (signatureColumns checks z) S).testBit (j.val + 1) then (1 : Bit) else 0) =
      ((checkMatrix checks) *ᵥ maskWord S) j := by
  unfold halfSignature
  rw [signatureColumns_list, maskedXor_eval_bit]
  change _ = ∑ i, wordOfNatMask 37 checks[j.val] i * maskWord S i
  apply Finset.sum_congr rfl
  intro i _
  rw [signatureColumn_bit_succ]
  simp only [List.getElem?_eq_getElem j.isLt, Option.map_some, Option.getD_some,
    decide_eq_true_eq, if_bit_dot_eq, dot_single_site_nat, maskWord, mul_comm]

theorem halfSignature_syndrome_bound (checks : List ℕ) (z : ℕ) (S : Finset (Fin 37))
    (hLen : checks.length = 18) :
    halfSignature (signatureColumns checks z) S / 2 < 2 ^ 18 := by
  let x := halfSignature (signatureColumns checks z) S
  have hx (j : ℕ) (hj : 18 ≤ j) : (x / 2).testBit j = false := by
    have he := Nat.testBit_div_two_pow (n := 1) x j
    change (x / 2).testBit j = x.testBit (j + 1) at he
    rw [he]
    have hnone : checks[j]? = none := List.getElem?_eq_none (by omega)
    dsimp [x]
    unfold halfSignature
    rw [signatureColumns_list, testBit_maskedXor]
    have hfold (bs : List Bool) (vs : List (Fin 37)) :
        (bs.zip (vs.map fun i => 2 * syndrome checks (1 <<< i.val) + dot z (1 <<< i.val))).foldr
            (fun p b => (p.1 && p.2.testBit (j + 1)) ^^ b) false = false := by
      induction bs generalizing vs with
      | nil => simp
      | cons b bs ih =>
        cases vs with
        | nil => simp
        | cons i vs =>
          simp [signatureColumn_bit_succ, hnone, ih]
    simpa only [List.map_ofFn, Function.comp_def] using
      hfold (List.ofFn fun i : Fin 37 => decide (i ∈ S)) (List.ofFn fun i : Fin 37 => i)
  have hm : x / 2 = (x / 2) % (2 ^ 18) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases h : j < 18
    · simp [h]
    · simp [h, hx j (by omega)]
  rw [hm]
  exact Nat.mod_lt _ (by decide)

theorem halfSignatures_same_syndrome (checks : List ℕ) (z : ℕ)
    (S T : Finset (Fin 37))
    (h : (checkMatrix checks) *ᵥ maskWord S = (checkMatrix checks) *ᵥ maskWord T)
    (hLen : checks.length = 18) :
    halfSignature (signatureColumns checks z) S / 2 =
      halfSignature (signatureColumns checks z) T / 2 := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 18
  · let t : Fin checks.length := ⟨j, by omega⟩
    have ha := Nat.testBit_div_two_pow (n := 1) (halfSignature (signatureColumns checks z) S) j
    have hb := Nat.testBit_div_two_pow (n := 1) (halfSignature (signatureColumns checks z) T) j
    change _ = (halfSignature (signatureColumns checks z) S).testBit (j + 1) at ha
    change _ = (halfSignature (signatureColumns checks z) T).testBit (j + 1) at hb
    rw [ha, hb]
    have he := (halfSignature_bit_succ checks z S t).trans
      ((congrFun h t).trans (halfSignature_bit_succ checks z T t).symm)
    cases hs : (halfSignature (signatureColumns checks z) S).testBit (j + 1) <;>
      cases ht : (halfSignature (signatureColumns checks z) T).testBit (j + 1) <;> simp_all [t]
  · have ha := halfSignature_syndrome_bound checks z S hLen
    have hb := halfSignature_syndrome_bound checks z T hLen
    have hp : 2 ^ 18 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le hp), Nat.testBit_eq_false_of_lt (hb.trans_le hp)]

end CriticalDepth.Q37BinaryData