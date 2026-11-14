import ExactGivensStep
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Prod

/-!
# Exact finite Givens elimination

The schedule visits the strict lower triangle in column order using only
the diagonal pivot and the current row. Each step maintains the zeroes
from preceding entries.
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix
open scoped BigOperators

noncomputable section

variable {N : ℕ}

private def orderedRows (i j : Fin N) (h : i ≠ j) : RowPair (Fin N) where
  toFun x := if x = 0 then i else j
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

private theorem orderedRows_zero (i j : Fin N) (h : i ≠ j) : orderedRows i j h 0 = i := rfl
private theorem orderedRows_one (i j : Fin N) (h : i ≠ j) : orderedRows i j h 1 = j := rfl

private theorem mem_range_orderedRows {i j r : Fin N} (h : i ≠ j) :
    r ∈ Set.range (orderedRows i j h) ↔ r = i ∨ r = j := by
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- A strict lower-triangular matrix entry in column-major order. -/
abbrev LowerEntry (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

private def entryBefore (p q : LowerEntry N) : Prop :=
  p.val.1 < q.val.1 ∨ p.val.1 = q.val.1 ∧ p.val.2 < q.val.2

private def entryStep (V : Operator (Fin N)) (p : LowerEntry N) : Operator (Fin N) :=
  givensStep V (orderedRows p.val.1 p.val.2 p.property.ne) p.val.1

private theorem entryStep_zero (V : Operator (Fin N)) (p : LowerEntry N) :
    (entryStep V p * V) p.val.2 p.val.1 = 0 := by
  exact givensStep_eliminates V (orderedRows p.val.1 p.val.2 p.property.ne) p.val.1

private theorem entryStep_preserves_before (V : Operator (Fin N)) (p q : LowerEntry N)
    (hpq : entryBefore p q) (hZero : ∀ r : LowerEntry N, entryBefore r q → V r.val.2 r.val.1 = 0) :
    (entryStep V q * V) p.val.2 p.val.1 = 0 := by
  let e := orderedRows q.val.1 q.val.2 q.property.ne
  have hp := hZero p hpq
  rcases hpq with hCol | ⟨hCol, hRow⟩
  · let r₀ : LowerEntry N := ⟨(p.val.1, q.val.1), hCol⟩
    let r₁ : LowerEntry N := ⟨(p.val.1, q.val.2), hCol.trans q.property⟩
    have hz := givensStep_preserves_zero_entries V e q.val.1 p.val.1
      (hZero r₀ (Or.inl hCol)) (hZero r₁ (Or.inl hCol)) p.val.2
    exact hz.trans hp
  · have hOutside : p.val.2 ∉ Set.range e := by
      rw [mem_range_orderedRows]
      rintro (h | h)
      · exact p.property.ne (hCol.trans h.symm)
      · exact hRow.ne h
    exact (givensStep_preserves_other_rows V e q.val.1 hOutside p.val.1).trans hp

private def entryKey (p : LowerEntry N) : ℕ :=
  p.val.1.val * N + p.val.2.val

private theorem entryKey_injective : Function.Injective (entryKey (N := N)) := by
  intro p q hpq
  have hRem (r : LowerEntry N) : entryKey r % N = r.val.2.val := by
    unfold entryKey
    rw [Nat.mul_comm r.val.1.val N, Nat.mul_add_mod, Nat.mod_eq_of_lt r.val.2.isLt]
  have h₂ : p.val.2 = q.val.2 := Fin.ext (by rw [← hRem p, hpq, hRem q])
  have h₁ : p.val.1 = q.val.1 := by
    have hN : 0 < N := p.val.1.pos
    apply Fin.ext
    have h₂val := congrArg Fin.val h₂
    unfold entryKey at hpq
    rw [h₂val] at hpq
    exact Nat.eq_of_mul_eq_mul_right hN (Nat.add_right_cancel hpq)
  exact Subtype.ext (Prod.ext h₁ h₂)

private theorem before_iff_entryKey_lt (p q : LowerEntry N) : entryBefore p q ↔ entryKey p < entryKey q := by
  unfold entryBefore entryKey
  constructor
  · rintro (h | ⟨h, h'⟩)
    · have h0 : p.val.1.val + 1 ≤ q.val.1.val := h
      have h1 := Nat.mul_le_mul_right N h0
      rw [Nat.add_mul, Nat.one_mul] at h1
      exact (Nat.add_lt_add_left p.val.2.isLt _).trans_le
        (h1.trans (Nat.le_add_right _ _))
    · have hh := congrArg Fin.val h
      rw [hh]
      exact Nat.add_lt_add_left h' _
  · intro h
    rcases lt_trichotomy p.val.1 q.val.1 with hb | hb | hb
    · exact Or.inl hb
    · right
      refine ⟨hb, ?_⟩
      rw [congrArg Fin.val hb] at h
      exact (Nat.lt_of_add_lt_add_left h : p.val.2.val < q.val.2.val)
    · have h0 : q.val.1.val + 1 ≤ p.val.1.val := hb
      have h1 := Nat.mul_le_mul_right N h0
      rw [Nat.add_mul, Nat.one_mul] at h1
      exact (h.not_gt ((Nat.add_lt_add_left q.val.2.isLt _).trans_le
        (h1.trans (Nat.le_add_right _ _)))).elim

/-- For a given starting matrix each scheduled step records its unitary
coefficient, including skipped zero-radius steps as identities. -/
def givensEliminationWord (V : Operator (Fin N)) : List (LowerEntry N) →
    List (Matrix.unitaryGroup (Fin N) ℂ)
  | [] => []
  | p :: tail =>
    (givensEliminationWord (entryStep V p * V) tail) ++
      [⟨entryStep V p, givensStep_isUnitary V _ _⟩]

private theorem givensEliminationWord_length (V : Operator (Fin N)) (l : List (LowerEntry N)) :
    (givensEliminationWord V l).length = l.length := by
  induction l generalizing V with
  | nil => rfl
  | cons p tail ih => simp [givensEliminationWord, ih]

/-- Each recorded elimination is identity or a two-level action with the
same ordered pivot and target row as the actual elimination step. -/
theorem givensEliminationWord_twoLevel_or_identity (V : Operator (Fin N))
    (l : List (LowerEntry N)) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (hU : U ∈ givensEliminationWord V l) :
    U = 1 ∨ ∃ e : RowPair (Fin N), ∃ A : Matrix.unitaryGroup (Fin 2) ℂ,
      U.val = twoLevel e A.val := by
  induction l generalizing V with
  | nil => simp [givensEliminationWord] at hU
  | cons p tail ih =>
    rw [givensEliminationWord, List.mem_append, List.mem_singleton] at hU
    rcases hU with hU | rfl
    · exact ih _ hU
    let e := orderedRows p.val.1 p.val.2 p.property.ne
    let a := V (e 0) p.val.1
    let b := V (e 1) p.val.1
    by_cases hr : givensRadius a b = 0
    · left
      apply Subtype.ext
      change givensStep V e p.val.1 = 1
      exact ite_eq_left hr
    · right
      refine ⟨e, ⟨givensBlock a b, givensBlock_isUnitary a b hr⟩, ?_⟩
      change givensStep V e p.val.1 = _
      exact ite_eq_right hr

/-- A triangular unitary is diagonal. The triangular inverse is its
conjugate transpose, so entries above the diagonal also vanish. -/
theorem unitary_eq_diagonal_of_upperTriangular (V : Operator (Fin N)) (hV : IsUnitary V)
    (htri : V.IsUpperTriangular) : V = diagonal (fun i => V i i) := by
  have hi : V⁻¹ = star V := Matrix.inv_eq_left_inv hV.1
  letI : Invertible V := invertibleOfLeftInverse V (star V) hV.1
  have hInv := blockTriangular_inv_of_blockTriangular htri
  ext i j
  by_cases he : i = j
  · subst j; rw [diagonal_apply_eq]
  rw [diagonal_apply_ne _ he]
  rcases lt_or_gt_of_ne he with h | h
  · have hs := hInv h
    rw [hi, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at hs
    exact star_eq_zero.mp hs
  · exact htri h

private abbrev entryLE {N : ℕ} (a b : LowerEntry N) : Prop :=
  entryKey a ≤ entryKey b

private instance {N : ℕ} : Std.Total (entryLE (N := N)) :=
  ⟨fun a b => le_total (entryKey a) (entryKey b)⟩

private instance {N : ℕ} : IsTrans (LowerEntry N) entryLE :=
  ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩

private instance {N : ℕ} : Std.Antisymm (entryLE (N := N)) :=
  ⟨fun a b h₁ h₂ => entryKey_injective (Nat.le_antisymm h₁ h₂)⟩

/-- The lower-triangle schedule, sorted by column and then row. -/
def givensSchedule (N : ℕ) : List (LowerEntry N) := by
  exact (Finset.univ : Finset (LowerEntry N)).sort entryLE

private theorem givensSchedule_before (N : ℕ) :
    (givensSchedule N).Pairwise entryBefore := by
  change ((Finset.univ : Finset (LowerEntry N)).sort entryLE).Pairwise entryBefore
  have h := (Finset.univ : Finset (LowerEntry N)).pairwise_sort entryLE
  have hn := (Finset.univ : Finset (LowerEntry N)).sort_nodup entryLE
  have hc := h.and hn
  exact hc.imp (fun {a b} hab => (before_iff_entryKey_lt a b).mpr
    (lt_of_le_of_ne hab.1 (fun he => hab.2 (entryKey_injective he))))

private theorem givensSchedule_mem (p : LowerEntry N) : p ∈ givensSchedule N := by
  change p ∈ (Finset.univ : Finset (LowerEntry N)).sort entryLE
  simp

private theorem givensEliminationWord_zeros (V : Operator (Fin N)) (l : List (LowerEntry N))
    (hSorted : l.Pairwise entryBefore)
    (done : Set (LowerEntry N)) (hCovered : ∀ p : LowerEntry N, p ∈ done ∨ p ∈ l)
    (hSortedAfter : ∀ p ∈ done, ∀ q ∈ l, entryBefore p q)
    (hPrior : ∀ p ∈ done, V p.val.2 p.val.1 = 0) :
    ∀ p : LowerEntry N,
      ((givensEliminationWord V l).prod.val * V) p.val.2 p.val.1 = 0 := by
  induction l generalizing V done with
  | nil =>
    intro p
    change (1 * V) p.val.2 p.val.1 = 0
    rw [Matrix.one_mul]
    exact hPrior p ((hCovered p).resolve_right (by simp))
  | cons q tail ih =>
    have hPair := List.pairwise_cons.mp hSorted
    let W := entryStep V q * V
    have hBefore : ∀ r : LowerEntry N, entryBefore r q → V r.val.2 r.val.1 = 0 := by
      intro r hr
      apply hPrior r
      rcases hCovered r with hd | hl
      · exact hd
      · rcases List.mem_cons.mp hl with he | hl
        · exact (lt_irrefl _ ((before_iff_entryKey_lt r r).mp (he ▸ hr))).elim
        · have hlt := (before_iff_entryKey_lt q r).mp (hPair.1 r hl)
          exact (hlt.not_gt ((before_iff_entryKey_lt r q).mp hr)).elim
    let nextDone : Set (LowerEntry N) := insert q done
    have hCov : ∀ p : LowerEntry N, p ∈ nextDone ∨ p ∈ tail := by
      intro p
      rcases hCovered p with hp | hp
      · exact Or.inl (Set.mem_insert_of_mem _ hp)
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact Or.inl (Set.mem_insert _ _)
        · exact Or.inr hp
    have hAfter : ∀ p ∈ nextDone, ∀ r ∈ tail, entryBefore p r := by
      intro p hp r hr
      rcases Set.mem_insert_iff.mp hp with rfl | hp
      · exact hPair.1 r hr
      · exact hSortedAfter p hp r (List.mem_cons_of_mem q hr)
    have hZero : ∀ r ∈ nextDone, W r.val.2 r.val.1 = 0 := by
      intro r hr
      rcases Set.mem_insert_iff.mp hr with rfl | hr
      · exact entryStep_zero V _
      · exact entryStep_preserves_before V r q (hSortedAfter r hr q (List.mem_cons_self ..)) hBefore
    intro p
    have h := ih W hPair.2 nextDone hCov hAfter hZero p
    unfold givensEliminationWord
    rw [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    change (((givensEliminationWord W tail).prod.val * entryStep V q) * V) p.val.2 p.val.1 = 0
    rw [Matrix.mul_assoc]
    exact h

/-- Every unitary is reduced to diagonal by the finite column-order
sequence of two-level rotations. -/
theorem unitary_givensElimination_diagonal (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ d : Fin N → ℂ, (givensEliminationWord U.val (givensSchedule N)).prod.val * U.val =
      diagonal d := by
  let V := (givensEliminationWord U.val (givensSchedule N)).prod * U
  have htri : V.val.IsUpperTriangular := by
    intro i j h
    let p : LowerEntry N := ⟨(j, i), h⟩
    exact givensEliminationWord_zeros _ _ (givensSchedule_before N) ∅
      (fun r => Or.inr (givensSchedule_mem r)) (by simp) (by simp) p
  exact ⟨fun i => V.val i i, unitary_eq_diagonal_of_upperTriangular V.val V.property htri⟩

private theorem lowerEntry_card (N : ℕ) : Fintype.card (LowerEntry N) = N.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))

/-- The schedule includes exactly one slot per strict lower entry.
An identity occupies a slot if its pivot radius was zero. -/
theorem givensEliminationWord_length_bound (V : Operator (Fin N)) :
    (givensEliminationWord V (givensSchedule N)).length = N * (N - 1) / 2 := by
  rw [givensEliminationWord_length]
  change ((Finset.univ : Finset (LowerEntry N)).sort entryLE).length = _
  rw [Finset.length_sort, Finset.card_univ, lowerEntry_card, Nat.choose_two_right]

/-- Reversing the eliminations yields the exact target and retains its
residual basis-state phases. -/
theorem unitary_eq_reverse_givens_with_phases (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ d : Fin N → ℂ, (∀ i, star (d i) * d i = 1) ∧
      U.val = ((givensEliminationWord U.val (givensSchedule N)).map (·⁻¹)).reverse.prod.val *
        diagonal d := by
  obtain ⟨d, hd⟩ := unitary_givensElimination_diagonal U
  let W := (givensEliminationWord U.val (givensSchedule N)).prod
  have hD : IsUnitary (diagonal d) := by
    rw [← hd]
    exact (W * U).property
  refine ⟨d, ?_, ?_⟩
  · intro i
    have h := congrArg (fun M : Operator (Fin N) => M i i) hD.1
    have hStar : star (diagonal d) = diagonal (fun j => star (d j)) := by
      ext a b
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      by_cases he : a = b
      · subst b; simp
      · rw [Matrix.diagonal_apply_ne _ he, Matrix.diagonal_apply_ne _ (Ne.symm he), star_zero]
    rw [hStar, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    exact h
  · rw [← List.prod_inv_reverse]
    change U.val = (W⁻¹).val * diagonal d
    rw [← hd]
    change U.val = (W⁻¹).val * (W.val * U.val)
    rw [← Matrix.mul_assoc, show (W⁻¹).val * W.val = 1 from W.property.1, Matrix.one_mul]

#print axioms unitary_eq_reverse_givens_with_phases

#print axioms givensEliminationWord_length_bound
#print axioms unitary_givensElimination_diagonal
#print axioms entryStep_preserves_before
#print axioms unitary_eq_diagonal_of_upperTriangular

end

end CriticalDepth.Manuscript20261114
