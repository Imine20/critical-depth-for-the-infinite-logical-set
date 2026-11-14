import CSSDisjointSolutionCounts
import CSSPermutationRigidity

/-!
Counting changed and unchanged row equations of a sparse automorphism.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators Matrix

local notation "𝔽" => ZMod 2
variable {n a : ℕ}

def changedRows (F : Matrix (Fin n) (Fin n) 𝔽) : Finset (Fin n) :=
  Finset.univ.filter fun i => F.row i ≠ (1 : Matrix (Fin n) (Fin n) 𝔽).row i

def rowVariables (F : Matrix (Fin n) (Fin n) 𝔽) (i : Fin n) : Finset (Fin n) :=
  insert i (Finset.univ.filter fun j => F i j ≠ 0)

theorem rowVariables_card (F : Matrix (Fin n) (Fin n) 𝔽) (i : Fin n) :
    (rowVariables F i).card ≤ wordWeight (F.row i) + 1 := by
  let P := fun j => F i j ≠ 0
  have h : (Finset.univ.filter P).card = wordWeight (F.row i) := by
    unfold wordWeight
    apply congrArg Finset.card
    have hfg (d₁ d₂ : DecidablePred P) :
        @Finset.filter _ P d₁ Finset.univ = @Finset.filter _ P d₂ Finset.univ :=
      @Finset.filter_congr_decidable _ _ P d₁ d₂
    exact hfg _ _
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right h.le 1)

theorem rowVariables_occur (F : Matrix (Fin n) (Fin n) 𝔽) (j : Fin n) :
    ((changedRows F).filter fun i => j ∈ rowVariables F i).card ≤
      wordWeight (fun i => F i j) + 1 := by
  classical
  let N := Finset.univ.filter fun i => F i j ≠ 0
  have h : ((changedRows F).filter fun i => j ∈ rowVariables F i) ⊆ insert j N := by
    intro i hi
    have hj := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_insert.mp hj with eq | hm
    · exact Finset.mem_insert.mpr (Or.inl eq.symm)
    · exact Finset.mem_insert_of_mem (show i ∈ N from Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm).2⟩)
  have hN : N.card = wordWeight (fun i => F i j) := by
    unfold wordWeight
    congr 1
    ext i
    simp [N]
  exact (Finset.card_le_card h).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right hN.le 1))

theorem changedRow_offDiagonal (F : Matrix (Fin n) (Fin n) 𝔽)
    (hF : Function.Surjective F.mulVec) {i : Fin n} (hi : i ∈ changedRows F) :
    ∃ j : Fin n, j ≠ i ∧ F i j = 1 := by
  classical
  by_contra! h
  have hz (j : Fin n) (hji : j ≠ i) : F i j = 0 := by
    rcases (show ∀ x : 𝔽, x = 0 ∨ x = 1 by decide) (F i j) with hh | hh
    · exact hh
    · exact (h j hji hh).elim
  have hd : F i i = 1 := by
    rcases (show ∀ x : 𝔽, x = 0 ∨ x = 1 by decide) (F i i) with hh | hh
    · obtain ⟨x, hx⟩ := hF (Pi.single i 1)
      have he := congrFun hx i
      change (∑ j, F i j * x j) = (Pi.single i (1 : 𝔽) : Fin n → 𝔽) i at he
      rw [Finset.sum_eq_zero (fun j _ => by
        by_cases hj : j = i
        · subst j; rw [hh, zero_mul]
        · rw [hz j hj, zero_mul]), Pi.single_eq_same] at he
      exact (zero_ne_one he).elim
    · exact hh
  have hne := (Finset.mem_filter.mp hi).2
  apply hne
  funext j
  by_cases hj : j = i
  · subst j
    simpa [Matrix.row] using hd
  · simpa [Matrix.row, Matrix.one_apply, hj, Ne.symm hj] using hz j hj

private theorem changedRow_pivot_determines
    (F : Matrix (Fin n) (Fin n) 𝔽) (S : Matrix (Fin a) (Fin a) 𝔽)
    (A B : Matrix (Fin n) (Fin a) 𝔽) (hA : F * A = A * S) (hB : F * B = B * S)
    (i j : Fin n) (hji : j ≠ i) (hFij : F i j = 1)
    (he : ∀ k ∈ rowVariables F i, k ≠ j → A.row k = B.row k) :
    A.row j = B.row j := by
  have hi : A.row i = B.row i := he i (Finset.mem_insert_self _ _) hji.symm
  have hr : (A * S).row i = (B * S).row i := by
    rw [Matrix.row_mul_eq_vecMul_row, Matrix.row_mul_eq_vecMul_row, hi]
  have hr' : (F * A).row i = (F * B).row i := by rw [hA, hB, hr]
  funext l
  have hsum := congrFun hr' l
  change (∑ k, F i k * A k l) = ∑ k, F i k * B k l at hsum
  have hrest :
      (∑ k ∈ Finset.univ.erase j, F i k * A k l) =
        ∑ k ∈ Finset.univ.erase j, F i k * B k l := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hz : F i k = 0
    · simp [hz]
    · have hm : k ∈ rowVariables F i := Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
      rw [show A k l = B k l from congrFun (he k hm (Finset.ne_of_mem_erase hk)) l]
  rw [← Finset.sum_erase_add Finset.univ (fun k => F i k * A k l) (Finset.mem_univ j),
    ← Finset.sum_erase_add Finset.univ (fun k => F i k * B k l) (Finset.mem_univ j),
    hrest, hFij, one_mul, one_mul] at hsum
  exact add_left_cancel hsum

theorem card_sparse_automorphism_changed_bound
    (F : Matrix (Fin n) (Fin n) 𝔽) (S : Matrix (Fin a) (Fin a) 𝔽) (R : ℕ)
    (hF : Function.Surjective F.mulVec)
    (hrow : ∀ i, wordWeight (F.row i) ≤ R) (hcol : ∀ j, wordWeight (fun i => F i j) ≤ R) :
    ∃ k ≤ n, (changedRows F).card ≤ k * ((R + 1) * (R + 1)) ∧
      (Finset.univ.filter fun A : Matrix (Fin n) (Fin a) 𝔽 => F * A = A * S).card ≤
        2 ^ (a * (n - k)) := by
  classical
  obtain ⟨rows, hrs, hrDis, hCount⟩ := exists_disjoint_family_card_bound
    (changedRows F) (rowVariables F) (R + 1) (R + 1)
    (fun i _ => ⟨i, Finset.mem_insert_self _ _⟩)
    (fun i _ => (rowVariables_card F i).trans (Nat.add_le_add_right (hrow i) 1))
    (fun j => (rowVariables_occur F j).trans (Nat.add_le_add_right (hcol j) 1))
  let S₀ : Finset (Fin n → Fin a → 𝔽) := Finset.univ.filter fun A =>
    F * Matrix.of A = Matrix.of A * S
  have hp (i : Fin n) (hi : i ∈ rows) := changedRow_offDiagonal F hF (hrs hi)
  let pivot (i : Fin n) : Fin n := if hi : i ∈ rows then (hp i hi).choose else i
  have hp' (i : Fin n) (hi : i ∈ rows) : pivot i ≠ i ∧ F i (pivot i) = 1 := by
    simpa [pivot, hi] using (hp i hi).choose_spec
  have hmem (i : Fin n) (hi : i ∈ rows) : pivot i ∈ rowVariables F i :=
    Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (hp' i hi).2 ▸ one_ne_zero⟩)
  have hsolve (i : Fin n) (hi : i ∈ rows) (x : Fin n → Fin a → 𝔽) (hx : x ∈ S₀)
      (y : Fin n → Fin a → 𝔽) (hy : y ∈ S₀)
      (h : ∀ j ∈ rowVariables F i, j ≠ pivot i → x j = y j) :
      x (pivot i) = y (pivot i) :=
    by
      have hxe : F * Matrix.of x = Matrix.of x * S := (Finset.mem_filter.mp hx).2
      have hye : F * Matrix.of y = Matrix.of y * S := (Finset.mem_filter.mp hy).2
      exact changedRow_pivot_determines F S (Matrix.of x) (Matrix.of y) hxe hye
        i (pivot i) (hp' i hi).1 (hp' i hi).2 h
  refine ⟨rows.card, by simpa using Finset.card_le_univ rows, hCount, ?_⟩
  have h := card_disjoint_solutions_le rows (rowVariables F) pivot hmem hrDis S₀ hsolve
  have hEq : S₀.card = (Finset.univ.filter fun A : Matrix (Fin n) (Fin a) 𝔽 => F * A = A * S).card := by
    apply congrArg Finset.card
    unfold S₀
    let P (A : Fin n → Fin a → 𝔽) := F * Matrix.of A = Matrix.of A * S
    have hfg (d₁ d₂ : DecidablePred P) :
        @Finset.filter _ P d₁ Finset.univ = @Finset.filter _ P d₂ Finset.univ :=
      @Finset.filter_congr_decidable _ _ P d₁ d₂
    exact hfg _ _
  rw [← hEq]
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul] at h
  exact h

#print axioms card_sparse_automorphism_changed_bound

end CriticalDepth.Manuscript20261114.CSSCheckSpaces