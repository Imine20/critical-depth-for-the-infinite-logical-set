import Q37PhaseBridge
import Q37CheckSpaces

/-!
# Applying the Q37 phase polynomials to words in each encoded coset
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript20261114.CSSCode

/-- The indicator coefficient vector of a set of rows. -/
def coefficientWord (a : ℕ) (S : Finset (Fin a)) : Fin a → CSSBit :=
  fun i => if i ∈ S then 1 else 0

/-- Evaluation of the block parity functional agrees with the parity
polynomial on the active coefficient positions. -/
theorem coefficient_eval_eq_supportParity (rows : List ℕ)
    (block : ℕ) (S : Finset (Fin rows.length)) :
    dotProduct (wordOfNatMask 37 block) (coefficientWord rows.length S ᵥ* checkMatrix rows) =
      (supportParity (coefficientSupport rows block) S : CSSBit) := by
  classical
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have hmul (i : Fin rows.length) :
      ((checkMatrix rows) *ᵥ wordOfNatMask 37 block) i =
        ((dot block rows[i] : ℕ) : CSSBit) := by
    change dotProduct (wordOfNatMask 37 rows[i]) (wordOfNatMask 37 block) = _
    rw [dotProduct_comm, dotProduct_wordOfNatMask]
  unfold dotProduct coefficientWord
  simp only [hmul, ite_mul, one_mul, zero_mul]
  have hparity (i : Fin rows.length) :
      (dot block rows[i] : CSSBit) = (if i ∈ coefficientSupport rows block then 1 else 0) := by
    have h : dot block rows[i] < 2 := by
      unfold dot
      exact Nat.mod_lt _ (by decide)
    unfold coefficientSupport
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    generalize dot block rows[i] = t at h ⊢
    interval_cases t <;> decide
  simp_rw [hparity]
  have hcard (T : Finset (Fin rows.length)) :
      (∑ i, if i ∈ S then (if i ∈ T then (1 : CSSBit) else 0) else 0) =
        ((T ∩ S).card : CSSBit) := by
    rw [show (T ∩ S).card = ((Finset.univ : Finset (Fin rows.length)).filter
        (fun i => i ∈ T ∧ i ∈ S)).card by congr 1; ext i; simp]
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]
  rw [hcard]
  unfold supportParity
  generalize hc : (coefficientSupport rows block ∩ S).card = m
  have hval : ((m : CSSBit)).val = m % 2 := ZMod.val_natCast 2 m
  have hm : m % 2 < 2 := Nat.mod_lt m (by decide)
  interval_cases m % 2
  · simpa using (ZMod.val_eq_zero _).mp hval
  · simpa using (ZMod.val_eq_one (by decide) _).mp hval

/-- Every row coefficient vector is indexed by its nonzero support. -/
theorem exists_coefficientWord (a : ℕ) (v : Fin a → CSSBit) :
    ∃ S : Finset (Fin a), coefficientWord a S = v := by
  classical
  refine ⟨Finset.univ.filter fun i => v i = 1, ?_⟩
  funext i
  have hv : v i = 0 ∨ v i = 1 := by
    generalize v i = b
    decide +revert
  rcases hv with h | h <;> simp [coefficientWord, h]

#print axioms coefficient_eval_eq_supportParity
#print axioms exists_coefficientWord

end CriticalDepth.Q37BinaryData
