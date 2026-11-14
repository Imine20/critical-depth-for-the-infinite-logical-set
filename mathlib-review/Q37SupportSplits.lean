import Q37MaskCertificate
import Q37NativeBlocks
import CSSCheckSpaces

/-!
The bounded-signature certificate applies to every binary word of weight at most six.
-/

open scoped BigOperators

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCheckSpaces

theorem wordSupport_card (x : Fin 37 → Bit) :
    (Finset.univ.filter (fun i => x i ≠ 0)).card = wordWeight x := by
  classical
  unfold wordWeight
  apply congrArg Finset.card
  have h (f g : DecidablePred (fun i => x i ≠ 0)) :
      @Finset.filter (Fin 37) (fun i => x i ≠ 0) f Finset.univ =
        @Finset.filter (Fin 37) (fun i => x i ≠ 0) g Finset.univ :=
    @Finset.filter_congr_decidable _ _ _ f g
  exact h _ _

theorem signedMask_split (x : Fin 37 → Bit) (h : wordWeight x < 7) :
    ∃ s t : Finset (Fin 37), s.card ≤ 3 ∧ t.card ≤ 3 ∧
      Disjoint s t ∧ x = (fun i => if i ∈ s then 1 else 0) +
        (fun i => if i ∈ t then 1 else 0) := by
  classical
  let S : Finset (Fin 37) := Finset.univ.filter fun i => x i ≠ 0
  have he : S.card = wordWeight x := by
    exact wordSupport_card x
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (min_le_left S.card 3)
  let t := S \ s
  have ht : t.card = S.card - min S.card 3 := by
    rw [Finset.card_sdiff_of_subset hs, hcard]
  refine ⟨s, t, hcard.trans_le (min_le_right _ _), by omega, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi
  · funext i
    change x i = (if i ∈ s then (1 : Bit) else 0) + (if i ∈ t then 1 else 0)
    have hb (hi : i ∈ S) : x i = 1 := by
      rcases (show ∀ y : Bit, y = 0 ∨ y = 1 by decide) (x i) with hn | hn
      · exact ((Finset.mem_filter.mp hi).2 hn).elim
      · exact hn
    by_cases hi : i ∈ s
    · have hit : i ∉ t := fun hj => (Finset.mem_sdiff.mp hj).2 hi
      simp [hi, hit, hb (hs hi)]
    · by_cases hj : i ∈ t
      · simp [hi, hj, hb ((Finset.mem_sdiff.mp hj).1)]
      · have hiS : i ∉ S := fun hS => hj (Finset.mem_sdiff.mpr ⟨hS, hi⟩)
        have hx : x i = 0 := by
          by_contra hp
          exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
        simp [hi, hj, hx]

theorem testBit_maskedXor (bits : List Bool) (values : List ℕ) (j : ℕ) :
    ((maskedXor bits values).testBit j) =
      (bits.zip values).foldr (fun p b => (p.1 && p.2.testBit j) ^^ b) false := by
  induction bits generalizing values with
  | nil => cases values <;> simp [maskedXor]
  | cons bit bits ih =>
      cases values with
      | nil => simp [maskedXor]
      | cons v vs =>
          cases bit <;>
            simp [maskedXor, Nat.testBit_xor, ih]

theorem maskedXor_eval_bit {n : ℕ} (a : Fin n → Bool) (v : Fin n → ℕ) (j : ℕ) :
    (if (maskedXor (List.ofFn a) (List.ofFn v)).testBit j then (1 : Bit) else 0) =
      ∑ i : Fin n, (if a i then 1 else 0) * (if (v i).testBit j then 1 else 0) := by
  induction n with
  | zero => simp [maskedXor]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ]
    let bits := List.ofFn (fun i : Fin n => a i.succ)
    let values := List.ofFn (fun i : Fin n => v i.succ)
    have ht := ih (fun i => a i.succ) (fun i => v i.succ)
    change (if (maskedXor bits values).testBit j then (1 : Bit) else 0) = _ at ht
    change (if (maskedXor (a 0 :: bits) (v 0 :: values)).testBit j then (1 : Bit) else 0) = _
    rw [← ht]
    cases ha : a 0 <;> cases hb : (v 0).testBit j <;>
      cases hc : (maskedXor bits values).testBit j <;>
      simp [maskedXor, ha, hb, hc, Nat.testBit_xor, show (1 : Bit) + 1 = 0 by decide]

theorem length_filter_ofFn (n : ℕ) (a : Fin n → Bool) :
    ((List.ofFn a).filter id).length = (Finset.univ.filter fun i => a i).card := by
  have hl (l : List Bool) : (l.filter id).length = (l.map Bool.toNat).sum := by
    induction l with
    | nil => rfl
    | cons b l ih => cases b <;> simp [ih, Nat.add_comm]
  rw [hl, List.map_ofFn, List.sum_ofFn, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases ha : a i <;> simp [Function.comp_apply, ha]

end CriticalDepth.Q37BinaryData