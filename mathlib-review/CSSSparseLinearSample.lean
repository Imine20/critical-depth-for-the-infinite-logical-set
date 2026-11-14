import CSSSparseLinearBudget

/-!
The sparse linear bad set in the planted binary column sample.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators Matrix

local notation "𝔽" => ZMod 2
variable {n a : ℕ}

def badSparseLinearMatrix (R : ℕ) (A : Matrix (Fin n) (Fin a) 𝔽) : Prop :=
  ∃ F : Matrix (Fin n) (Fin n) 𝔽, ∃ S : Matrix (Fin a) (Fin a) 𝔽,
    F ≠ 1 ∧ S ≠ 1 ∧ Function.Surjective F.mulVec ∧
    (∀ i, wordWeight (F.row i) ≤ R) ∧ (∀ j, wordWeight (fun i => F i j) ≤ R) ∧
    F * A = A * S

theorem card_badSparseLinearMatrix_scaled (R B : ℕ) (hn : 0 < n)
    (hB : ((R + 1) * (R + 1)) * (2 * B + 1) ≤ a)
    (hcount : n * ((R + 1) * n ^ R) ≤ 2 ^ B)
    [DecidablePred (fun A : Matrix (Fin n) (Fin a) 𝔽 => badSparseLinearMatrix R A)] :
    (Finset.univ.filter fun A : Matrix (Fin n) (Fin a) 𝔽 => badSparseLinearMatrix R A).card *
        2 ^ (n / 2) ≤ n * 2 ^ (a * a + a * n) := by
  classical
  let MA := Matrix (Fin n) (Fin a) 𝔽
  let MF := Matrix (Fin n) (Fin n) 𝔽
  let MS := Matrix (Fin a) (Fin a) 𝔽
  let rows (u : Fin n) : Finset MF := Finset.univ.filter fun F =>
    (changedRows F).card = u.val + 1 ∧ ∀ i, wordWeight (F.row i) ≤ R
  let fiber (F : MF) (S : MS) : Finset MA := Finset.univ.filter fun A =>
    S ≠ 1 ∧ Function.Surjective F.mulVec ∧
    (∀ i, wordWeight (F.row i) ≤ R) ∧
    (∀ j, wordWeight (fun i => F i j) ≤ R) ∧ F * A = A * S
  let group (u : Fin n) : Finset MA := (rows u).biUnion fun F =>
    (Finset.univ : Finset MS).biUnion (fiber F)
  have hcover : (Finset.univ.filter fun A : MA => badSparseLinearMatrix R A) ⊆
      (Finset.univ : Finset (Fin n)).biUnion group := by
    intro A h
    obtain ⟨F, S, hF, hS, hSurj, hRow, hCol, he⟩ := (Finset.mem_filter.mp h).2
    have hne : (changedRows F).card ≠ 0 := by
      intro hzero
      apply hF
      have hnil := Finset.card_eq_zero.mp hzero
      ext i j
      have hi : F.row i = (1 : MF).row i := by
        by_contra hh
        have hm : i ∈ changedRows F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
        rw [hnil] at hm
        exact Finset.notMem_empty _ hm
      exact congrFun hi j
    have hcard : (changedRows F).card ≤ n := by simpa using Finset.card_le_univ (changedRows F)
    let u : Fin n := ⟨(changedRows F).card - 1, by omega⟩
    refine Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨F, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [u]; omega, hRow⟩
    · exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS, hSurj, hRow, hCol, he⟩⟩
  have hMS : (Finset.univ : Finset MS).card = 2 ^ (a * a) := by
    rw [Finset.card_univ]
    change Fintype.card (Fin a → Fin a → 𝔽) = _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul]
  have hRowCount (u : Fin n) : (rows u).card ≤ 2 ^ ((u.val + 1) * B) := by
    have hb := card_sparse_matrices_filter_le (1 : MF) R (u.val + 1) hn
    change (rows u).card ≤ _
    have he : (rows u).card ≤ (n * ((R + 1) * n ^ R)) ^ (u.val + 1) := by
      let P (F : MF) := (rowChangesFrom (1 : MF) F).card = u.val + 1 ∧
        ∀ i, wordWeight (F.row i) ≤ R
      have hd (d₁ d₂ : DecidablePred P) :
          @Finset.filter MF P d₁ Finset.univ = @Finset.filter MF P d₂ Finset.univ :=
        @Finset.filter_congr_decidable _ _ P d₁ d₂
      have hp : rows u = (Finset.univ.filter P) := by
        change (Finset.univ.filter P) = Finset.univ.filter P
        exact hd _ _
      rw [hp]
      exact hb
    refine he.trans ?_
    rw [Nat.mul_comm (u.val + 1) B, pow_mul]
    exact Nat.pow_le_pow_left hcount _
  have hfiber (u : Fin n) (F : MF) (h : F ∈ rows u) (S : MS) :
      (fiber F S).card * 2 ^ (n / 2 + (u.val + 1) * B) ≤ 2 ^ (a * n) := by
    by_cases hgood : S ≠ 1 ∧ Function.Surjective F.mulVec ∧
        (∀ i, wordWeight (F.row i) ≤ R) ∧ (∀ j, wordWeight (fun i => F i j) ≤ R)
    · have he : fiber F S = Finset.univ.filter fun A : MA => F * A = A * S := by
        ext A
        simp [fiber, hgood.1, hgood.2.1, hgood.2.2.1, hgood.2.2.2]
      rw [he, ← (Finset.mem_filter.mp h).2.1]
      exact sparse_linear_fixed_count_scaled F S R B hgood.2.1 hgood.1 hgood.2.2.1 hgood.2.2.2 hB
    · have he : fiber F S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A ha
        obtain ⟨hs, hsurj, hrow, hcol, _⟩ := (Finset.mem_filter.mp ha).2
        exact hgood ⟨hs, hsurj, hrow, hcol⟩
      simp [he]
  have hGroup (u : Fin n) : (group u).card * 2 ^ (n / 2) ≤ 2 ^ (a * a + a * n) := by
    have hg : (group u).card ≤ ∑ F ∈ rows u, ∑ S : MS, (fiber F S).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
    have hscaled : (group u).card * 2 ^ (n / 2 + (u.val + 1) * B) ≤
        2 ^ ((u.val + 1) * B) * 2 ^ (a * a + a * n) := by
      calc
        _ ≤ (∑ F ∈ rows u, ∑ S : MS, (fiber F S).card) * 2 ^ (n / 2 + (u.val + 1) * B) :=
          Nat.mul_le_mul_right _ hg
        _ ≤ ∑ _F ∈ rows u, ∑ _S : MS, 2 ^ (a * n) := by
          simp only [Finset.sum_mul]
          exact Finset.sum_le_sum fun F hF => Finset.sum_le_sum fun S _ => hfiber u F hF S
        _ = (rows u).card * 2 ^ (a * a + a * n) := by
          simp only [pow_add, Finset.sum_const, nsmul_eq_mul, hMS, Nat.cast_id]
        _ ≤ _ := Nat.mul_le_mul_right _ (hRowCount u)
    rw [pow_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ ((u.val + 1) * B))] at hscaled
    exact Nat.le_of_mul_le_mul_right hscaled (by positivity)
  calc
    _ ≤ ((Finset.univ : Finset (Fin n)).biUnion group).card * 2 ^ (n / 2) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
    _ ≤ (∑ u : Fin n, (group u).card) * 2 ^ (n / 2) :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ ≤ ∑ _u : Fin n, 2 ^ (a * a + a * n) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun u _ => hGroup u
    _ = n * 2 ^ (a * a + a * n) := by simp

#print axioms card_badSparseLinearMatrix_scaled

end CriticalDepth.Manuscript20261114.CSSCheckSpaces