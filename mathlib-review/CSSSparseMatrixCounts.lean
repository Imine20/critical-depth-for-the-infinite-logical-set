import CSSWeightBallCounts
import Mathlib.Data.Nat.Choose.Bounds

/-!
A sparse binary matrix is determined by the rows where it differs from a fixed
reference matrix and by its row words at those positions. The reference matrix
can be zero for a sparse quadratic form or the identity for an automorphism.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators Matrix

variable {n : ℕ}

local notation "BM" => Matrix (Fin n) (Fin n) (ZMod 2)

/-- Rows where the candidate matrix differs from the reference matrix. -/
def rowChangesFrom (F₀ F : BM) : Finset (Fin n) :=
  Finset.univ.filter fun i => F.row i ≠ F₀.row i

@[simp] theorem mem_rowChangesFrom {F₀ F : BM} {i : Fin n} :
    i ∈ rowChangesFrom F₀ F ↔ F.row i ≠ F₀.row i := by
  simp [rowChangesFrom]

private abbrev SparseRows (F₀ : BM) (R : ℕ) (s : Finset (Fin n)) :=
  {F : BM // rowChangesFrom F₀ F = s ∧ ∀ i ∈ s, wordWeight (F.row i) ≤ R}

private theorem card_sparseRows_le (F₀ : BM) (R : ℕ) (s : Finset (Fin n)) :
    Nat.card (SparseRows F₀ R s) ≤ (natShells n R) ^ s.card := by
  classical
  let rowWords := {x : BW n // wordWeight x ≤ R}
  let f : SparseRows F₀ R s → (s → rowWords) :=
    fun F i => ⟨F.val.row i, F.property.2 i i.property⟩
  have hf : Function.Injective f := by
    intro F G h
    apply Subtype.ext
    ext i j
    by_cases hi : i ∈ s
    · have hrow : F.val.row i = G.val.row i := congrArg Subtype.val (congrFun h ⟨i, hi⟩)
      exact congrFun hrow j
    · have eq_reference (H : SparseRows F₀ R s) : H.val.row i = F₀.row i := by
        by_contra hn
        have hm : i ∈ rowChangesFrom F₀ H.val := mem_rowChangesFrom.mpr hn
        exact hi (H.property.1 ▸ hm)
      exact congrFun ((eq_reference F).trans (eq_reference G).symm) j
  have hwords : Nat.card rowWords ≤ natShells n R := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_binary_atMost_le n R
  calc
    Nat.card (SparseRows F₀ R s) ≤ Nat.card (s → rowWords) :=
      Nat.card_le_card_of_injective f hf
    _ = Nat.card rowWords ^ s.card := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ↥s), Fintype.card_coe]
    _ ≤ (natShells n R) ^ s.card := Nat.pow_le_pow_left hwords _

/-- Exact support-size bound with the finite binary Hamming ball count. -/
theorem card_sparse_matrices_shell_le (F₀ : BM) (R u : ℕ) :
    Nat.card {F : BM // (rowChangesFrom F₀ F).card = u ∧
      ∀ i ∈ rowChangesFrom F₀ F, wordWeight (F.row i) ≤ R} ≤
      n.choose u * (natShells n R) ^ u := by
  classical
  let supports := Finset.powersetCard u (Finset.univ : Finset (Fin n))
  let S := {F : BM // (rowChangesFrom F₀ F).card = u ∧
    ∀ i ∈ rowChangesFrom F₀ F, wordWeight (F.row i) ≤ R}
  let T := Σ s : supports, SparseRows F₀ R s.val
  let f : S → T := fun F =>
    ⟨⟨rowChangesFrom F₀ F.val, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, F.property.1⟩⟩,
      ⟨F.val, rfl, F.property.2⟩⟩
  have hf : Function.Injective f := fun F G h =>
    Subtype.ext (congrArg (fun y : T => y.2.val) h)
  calc
    Nat.card S ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    _ = ∑ s : supports, Nat.card (SparseRows F₀ R s.val) := Nat.card_sigma
    _ ≤ ∑ _s : supports, (natShells n R) ^ u := by
      apply Finset.sum_le_sum
      intro s _
      have hc := (Finset.mem_powersetCard.mp s.property).2
      simpa only [hc] using card_sparseRows_le F₀ R s.val
    _ = n.choose u * (natShells n R) ^ u := by
      have hcard : supports.card = n.choose u := by
        simp only [supports, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe,
        Nat.cast_id, hcard]

theorem natShells_le (n R : ℕ) (hn : 0 < n) :
    natShells n R ≤ (R + 1) * n ^ R := by
  unfold natShells
  calc
    (∑ j ∈ Finset.range (R + 1), n.choose j) ≤ ∑ _j ∈ Finset.range (R + 1), n ^ R := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow n j).trans
        (Nat.pow_le_pow_right hn (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = (R + 1) * n ^ R := by simp [nsmul_eq_mul]

/-- Polynomial base bound for a prescribed support size, valid for any reference. -/
theorem card_sparse_matrices_le (F₀ : BM) (R u : ℕ) (hn : 0 < n) :
    Nat.card {F : BM // (rowChangesFrom F₀ F).card = u ∧
      ∀ i ∈ rowChangesFrom F₀ F, wordWeight (F.row i) ≤ R} ≤
      (n * ((R + 1) * n ^ R)) ^ u :=
  (card_sparse_matrices_shell_le F₀ R u).trans (by
    rw [mul_pow]
    exact Nat.mul_le_mul (Nat.choose_le_pow n u)
      (Nat.pow_le_pow_left (natShells_le n R hn) u))

theorem card_sparse_matrices_filter_le (F₀ : BM) (R u : ℕ) (hn : 0 < n)
    [DecidablePred (fun F : BM => (rowChangesFrom F₀ F).card = u ∧
      ∀ i, wordWeight (F.row i) ≤ R)] :
    (Finset.univ.filter fun F : BM => (rowChangesFrom F₀ F).card = u ∧
      ∀ i, wordWeight (F.row i) ≤ R).card ≤ (n * ((R + 1) * n ^ R)) ^ u := by
  classical
  let S := {F : BM // (rowChangesFrom F₀ F).card = u ∧ ∀ i, wordWeight (F.row i) ≤ R}
  let T := {F : BM // (rowChangesFrom F₀ F).card = u ∧
    ∀ i ∈ rowChangesFrom F₀ F, wordWeight (F.row i) ≤ R}
  let f : S → T := fun F => ⟨F.val, F.property.1, fun i _ => F.property.2 i⟩
  have hf : Function.Injective f := fun F G h => Subtype.ext (congrArg (fun x : T => x.val) h)
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact (Nat.card_le_card_of_injective f hf).trans (card_sparse_matrices_le F₀ R u hn)

#print axioms card_sparse_matrices_shell_le
#print axioms card_sparse_matrices_le
#print axioms card_sparse_matrices_filter_le

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
