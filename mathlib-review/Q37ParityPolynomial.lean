import CriticalDepthMathlib

/-!
# Low-degree parity certificates

A sum of binary parities of linear forms, reduced modulo 2^r, has a
multilinear polynomial of degree at most r. Such a polynomial is determined
by its evaluations at masks of weight at most r.
-/

namespace CriticalDepth.Q37BinaryData

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- Parity on a support, encoded by the integer 0 or 1. -/
def supportParity (L S : Finset ι) : ℤ :=
  if (L ∩ S).card % 2 = 0 then 0 else 1

private def parityCoefficient (r : ℕ) (T L : Finset ι) : ZMod (2 ^ r) :=
  if T.Nonempty ∧ T ⊆ L then ((-2 : ℤ) ^ (T.card - 1) : ZMod (2 ^ r)) else 0

private theorem supportParity_insert (L S : Finset ι) (i : ι) (hi : i ∉ S) :
    supportParity L (insert i S) =
      supportParity L S + (if i ∈ L then 1 else 0) -
        2 * supportParity L S * (if i ∈ L then 1 else 0) := by
  have intersection : L ∩ insert i S = if i ∈ L then insert i (L ∩ S) else L ∩ S := by
    ext x
    by_cases hx : i ∈ L <;> simp only [hx, ite_true, ite_false, Finset.mem_insert,
      Finset.mem_inter] <;> by_cases he : x = i <;> simp_all
  have hni : i ∉ L ∩ S := fun hm => hi (Finset.mem_inter.mp hm).2
  unfold supportParity
  rw [intersection]
  by_cases him : i ∈ L
  · simp only [him, ite_true, Finset.card_insert_of_notMem hni, Int.mul_one]
    split <;> split <;> norm_num at * <;> omega
  · simp [him]

/-- The integer parity has the usual alternating multilinear expansion.
Each nonempty monomial of size k has coefficient (-2)^(k-1). -/
private theorem supportParity_expanded (L S : Finset ι) :
    supportParity L S = ∑ T ∈ S.powerset,
      if T.Nonempty ∧ T ⊆ L then (-2 : ℤ) ^ (T.card - 1) else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [supportParity]
  | @insert i S hi ih =>
    rw [supportParity_insert L S i hi, Finset.sum_powerset_insert hi, ← ih]
    by_cases hil : i ∈ L
    · simp only [hil, ite_true, mul_one]
      -- The second sum adds a singleton and multiplies every old nonempty
      -- coefficient by -2.
      have hterm (T : Finset ι) (hT : T ∈ S.powerset) :
          (if (insert i T).Nonempty ∧ insert i T ⊆ L then
            (-2 : ℤ) ^ ((insert i T).card - 1) else 0) =
          (if T = ∅ then 1 else 0) +
            (-2 : ℤ) * (if T.Nonempty ∧ T ⊆ L then (-2 : ℤ) ^ (T.card - 1) else 0) := by
        have hni : i ∉ T := fun h => hi (Finset.mem_powerset.mp hT h)
        by_cases he : T = ∅
        · simp [he, hil]
        have hn := Finset.nonempty_iff_ne_empty.mpr he
        have hc : T.card - 1 + 1 = T.card := by
          have := Finset.card_pos.mpr hn
          omega
        by_cases hTL : T ⊆ L
        · have hin : insert i T ⊆ L := Finset.insert_subset hil hTL
          simp [Finset.card_insert_of_notMem hni, he, hn, hin, hTL]
          conv_lhs => rw [← hc, pow_succ, mul_comm]
          ring
        · have hin : ¬ insert i T ⊆ L := fun h => hTL ((Finset.subset_insert i T).trans h)
          simp [he, hn, hin, hTL]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← ih]
      have hsingle : (∑ T ∈ S.powerset, if T = ∅ then (1 : ℤ) else 0) = 1 := by
        rw [Finset.sum_eq_single (∅ : Finset ι)]
        · simp
        · intro T _ hne
          simp [hne]
        · simp
      rw [hsingle]
      ring
    · have hzero : (∑ T ∈ S.powerset,
          if (insert i T).Nonempty ∧ insert i T ⊆ L then
            (-2 : ℤ) ^ ((insert i T).card - 1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro T _
        have hnot : ¬ insert i T ⊆ L := fun h => hil (h (Finset.mem_insert_self i T))
        simp [hnot]
      rw [hzero]
      simp [hil]

/-- Reducing an old parity coefficient modulo 2^r kills all monomials
whose support has more than r elements. -/
private theorem parityCoefficient_zero_of_card_lt (r : ℕ) (T L : Finset ι)
    (hT : r < T.card) : parityCoefficient r T L = 0 := by
  unfold parityCoefficient
  split
  · have hpow : ((-2 : ℤ) ^ r : ZMod (2 ^ r)) = 0 := by
      have h2 : (2 : ZMod (2 ^ r)) ^ r = 0 := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2 ^ r)
      rw [Int.cast_neg, Int.cast_ofNat, neg_pow, h2, mul_zero]
    have he : T.card - 1 = r + (T.card - 1 - r) := by omega
    rw [he, pow_add, hpow, zero_mul]
  · rfl

omit [DecidableEq ι] in
/-- Evaluation on small masks determines a bounded-degree multilinear
polynomial, with coefficients in any additive group. -/
theorem sum_powerset_eq_zero_of_small_masks {R : Type*} [AddCommGroup R]
    (degree : ℕ) (c : Finset ι → R)
    (hdegree : ∀ T, degree < T.card → c T = 0)
    (hsmall : ∀ S : Finset ι, S.card ≤ degree → ∑ T ∈ S.powerset, c T = 0)
    (S : Finset ι) : ∑ T ∈ S.powerset, c T = 0 := by
  classical
  have hc (n : ℕ) : ∀ T : Finset ι, T.card = n → c T = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT
      by_cases hsize : degree < T.card
      · exact hdegree T hsize
      have hsum := hsmall T (by omega)
      have hsingle : ∑ U ∈ T.powerset, c U = c T := by
        apply Finset.sum_eq_single T
        · intro U hU hne
          have hsub := Finset.mem_powerset.mp hU
          have hlt : U.card < n := by
            rw [← hT]
            exact Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
          exact ih U.card hlt U rfl
        · exact fun h => False.elim (h (Finset.mem_powerset.mpr subset_rfl))
      rwa [hsingle] at hsum
  exact Finset.sum_eq_zero fun T _ => hc T.card T rfl

/-- A finite sum of affine binary parities is determined modulo 2^r by
the evaluations on coefficient masks of Hamming weight at most r. -/
theorem affineParitySum_of_small_masks {β : Type*} (blocks : Finset β)
    (support : β → Finset ι) (sign : β → ℤ) (r : ℕ) (constant : ZMod (2 ^ r))
    (hsmall : ∀ S : Finset ι, S.card ≤ r →
      ∑ b ∈ blocks, (sign b : ZMod (2 ^ r)) * (supportParity (support b) S : ZMod (2 ^ r)) =
        constant) (S : Finset ι) :
    ∑ b ∈ blocks, (sign b : ZMod (2 ^ r)) * (supportParity (support b) S : ZMod (2 ^ r)) =
      constant := by
  classical
  let c (T : Finset ι) : ZMod (2 ^ r) :=
    (∑ b ∈ blocks, (sign b : ZMod (2 ^ r)) * parityCoefficient r T (support b)) -
      (if T = ∅ then constant else 0)
  have hexp (A : Finset ι) :
      ∑ T ∈ A.powerset, c T =
        (∑ b ∈ blocks, (sign b : ZMod (2 ^ r)) * (supportParity (support b) A : ZMod (2 ^ r))) -
        constant := by
    simp only [c, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.mul_sum]
      congr 1
      rw [supportParity_expanded (support b) A, Int.cast_sum]
      exact Finset.sum_congr rfl fun T _ => by
        simp only [parityCoefficient, apply_ite (Int.cast : ℤ → ZMod (2 ^ r)), Int.cast_pow, Int.cast_zero]
    · rw [Finset.sum_eq_single (∅ : Finset ι)]
      · simp
      · intro T _ hne
        simp [hne]
      · simp
  have hz := sum_powerset_eq_zero_of_small_masks r c (fun T hT => by
    have hn : T ≠ ∅ := by intro he; simp [he] at hT
    simp [c, hn, parityCoefficient_zero_of_card_lt r T _ hT])
    (fun A hA => by rw [hexp, hsmall A hA, sub_self]) S
  rw [hexp, sub_eq_zero] at hz
  exact hz

#print axioms sum_powerset_eq_zero_of_small_masks
#print axioms affineParitySum_of_small_masks

end CriticalDepth.Q37BinaryData