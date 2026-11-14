import ShorPermutationAction

/-!
# Whole fixed space of the rectangular Shor check operators

Even row translations connect all strings in a common-parity coset.
The diagonal checks compare the parities of two rows and annihilate
the coordinates with unequal row parities in any common fixed vector.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.BinaryPermutationUnitary
open scoped BigOperators

variable {rows columns : ℕ}

private theorem rowParity_add (x y : Mask rows columns) (i : Fin rows) :
    rowParity (x + y) i = rowParity x i + rowParity y i := by
  simp [rowParity, Pi.add_apply, Finset.sum_add_distrib]

private theorem rowParity_sub (x y : Mask rows columns) (i : Fin rows) :
    rowParity (x - y) i = rowParity x i - rowParity y i := by
  simp [rowParity, Pi.sub_apply, Finset.sum_sub_distrib]

private theorem bit_sub_eq_add (x y : Bit) : x - y = x + y := by
  decide +revert

/-- The phase of the product of the two full-row Z checks at the basis word x. -/
def rowPairCheckPhase (i j : Fin rows) (x : Mask rows columns) : ℂ :=
  if rowParity x i = rowParity x j then 1 else -1

/-- Matrix of the full-row pair check, diagonal in the computational basis. -/
noncomputable def shorZPairCheck (i j : Fin rows) :
    Matrix (Mask rows columns) (Mask rows columns) ℂ :=
  Matrix.diagonal (rowPairCheckPhase i j)

theorem shorZPairCheck_mulVec (i j : Fin rows) (v : Mask rows columns → ℂ)
    (x : Mask rows columns) :
    (shorZPairCheck i j).mulVec v x = rowPairCheckPhase i j x * v x := by
  simp [shorZPairCheck, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul]

theorem shorXCheck_mulVec (a : Mask rows columns) (v : Mask rows columns → ℂ)
    (x : Mask rows columns) :
    (basisPermutation (translate a)).mulVec v x = v (x + a) := by
  classical
  have hentry (y : Mask rows columns) :
      basisPermutation (translate a) x y = if (translate a).symm x = y then 1 else 0 := by
    simp [basisPermutation_apply, Equiv.symm_apply_eq]
  have htranslate : (translate a).symm x = x + a := by
    change x - a = x + a
    funext i
    exact bit_sub_eq_add (x i) (a i)
  simp only [Matrix.mulVec, dotProduct, hentry, htranslate, ite_mul, one_mul, zero_mul]
  simp

theorem shorZPairCheck_fixed_iff (v : Mask rows columns → ℂ) :
    (∀ i j : Fin rows, (shorZPairCheck i j).mulVec v = v) ↔
      ∀ x, (∃ i j : Fin rows, rowParity x i ≠ rowParity x j) → v x = 0 := by
  constructor
  · rintro h x ⟨i, j, hne⟩
    have hentry := congrFun (h i j) x
    rw [shorZPairCheck_mulVec, rowPairCheckPhase, ite_eq_right hne] at hentry
    linear_combination (-1 / 2 : ℂ) * hentry
  · intro h i j
    funext x
    rw [shorZPairCheck_mulVec]
    by_cases hp : rowParity x i = rowParity x j
    · simp [rowPairCheckPhase, hp]
    · simp [h x ⟨i, j, hp⟩]

private theorem shorAmplitude_ne_zero (rows columns : ℕ) :
    shorAmplitude rows columns ≠ 0 := by
  intro hz
  have hcard : (parityWordCount rows columns : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (parityWordCount_pos rows columns))
  have hs := shorAmplitude_square rows columns
  rw [hz, mul_zero] at hs
  exact (inv_ne_zero hcard) hs.symm

theorem shorEncoding_mulVec_apply (r : Fin rows) (v : Bit → ℂ)
    (x : Mask rows (columns + 1)) :
    (shorEncoding rows columns).mulVec v x =
      if x ∈ parityWords (rowParity x r) then
        shorAmplitude rows columns * v (rowParity x r)
      else 0 := by
  classical
  have himplies (b : Bit) (hb : x ∈ parityWords b) : b = rowParity x r :=
    ((parityWords_mem_iff b x).mp hb r).symm
  by_cases h : x ∈ parityWords (rowParity x r)
  · rw [ite_eq_left h]
    unfold Matrix.mulVec dotProduct
    rw [Finset.sum_eq_single (rowParity x r)]
    · simp [shorEncoding, h]
    · intro b _ hb
      have hx : x ∉ parityWords b := fun hh => hb (himplies b hh)
      simp [shorEncoding, hx]
    · simp
  · rw [ite_eq_right h]
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_eq_zero
    intro b _
    have hx : x ∉ parityWords b := by
      intro hb
      exact h (himplies b hb ▸ hb)
    simp [shorEncoding, hx]

/-- The encoded subspace is the entire common fixed space of the X row
checks and the Z row-pair checks on the binary computational basis. -/
theorem shorEncoding_range_eq_fixedChecks (r : Fin rows) :
    Set.range (fun v => (shorEncoding rows columns).mulVec v) =
      {v | (∀ a : Mask rows (columns + 1), xChecks a →
          (basisPermutation (translate a)).mulVec v = v) ∧
        ∀ i j : Fin rows, (shorZPairCheck i j).mulVec v = v} := by
  classical
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨?_, (shorZPairCheck_fixed_iff _).mpr ?_⟩
    · intro a ha
      funext x
      rw [shorXCheck_mulVec]
      change (shorEncoding rows columns).mulVec w (x + a) =
        (shorEncoding rows columns).mulVec w x
      rw [shorEncoding_mulVec_apply r, shorEncoding_mulVec_apply r]
      have hp (i : Fin rows) : rowParity (x + a) i = rowParity x i := by
        rw [rowParity_add, ha i, add_zero]
      simp only [parityWords_mem_iff, hp]
    · rintro x ⟨i, j, hne⟩
      change (shorEncoding rows columns).mulVec w x = 0
      have h : x ∉ parityWords (rowParity x r) := by
        intro hm
        have he := (parityWords_mem_iff _ x).mp hm
        exact hne ((he i).trans (he j).symm)
      rw [shorEncoding_mulVec_apply r, ite_eq_right h]
  · rintro ⟨hX, hZ⟩
    let representative (b : Bit) := parityWord b (0 : Fin rows → Fin columns → Bit)
    refine ⟨fun b => (shorAmplitude rows columns)⁻¹ * v (representative b), ?_⟩
    funext x
    change (shorEncoding rows columns).mulVec
      (fun b => (shorAmplitude rows columns)⁻¹ * v (representative b)) x = v x
    rw [shorEncoding_mulVec_apply r]
    by_cases h : x ∈ parityWords (rowParity x r)
    · rw [ite_eq_left h, ← mul_assoc, mul_inv_cancel₀ (shorAmplitude_ne_zero rows columns), one_mul]
      let b := rowParity x r
      let a := x - representative b
      have ha : xChecks a := by
        intro i
        change rowParity (x - representative b) i = 0
        rw [rowParity_sub, (parityWords_mem_iff b x).mp h i, rowParity_parityWord, sub_self]
      have hx := congrFun (hX a ha) (representative b)
      rw [shorXCheck_mulVec] at hx
      change v (representative b + (x - representative b)) = _ at hx
      rw [add_comm (representative b), sub_add_cancel] at hx
      exact hx.symm
    · rw [ite_eq_right h]
      symm
      apply (shorZPairCheck_fixed_iff _).mp hZ x
      by_contra hn
      apply h
      apply (parityWords_mem_iff _ x).mpr
      intro i
      by_contra hi
      exact hn ⟨i, r, hi⟩

#print axioms shorXCheck_mulVec
#print axioms shorZPairCheck_mulVec
#print axioms shorZPairCheck_fixed_iff
#print axioms shorEncoding_range_eq_fixedChecks

end CriticalDepth.FaultShorSaturation
