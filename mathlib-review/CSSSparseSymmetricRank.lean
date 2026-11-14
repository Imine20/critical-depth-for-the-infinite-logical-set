import CSSPlantedHyperplane
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank of sparse symmetric matrices on the planted hyperplane

The nonzero columns lie in the union of the supports of a row basis.
Symmetry identifies the active row and column sets. Restricting to the
planted hyperplane loses at most one dimension, and a nonzero row of
weight below the planted word survives that restriction.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

noncomputable section

open Matrix
open scoped BigOperators Matrix

variable {n : ℕ}

def nonzeroRows (Q : Matrix (Fin n) (Fin n) (ZMod 2)) : Finset (Fin n) :=
  Finset.univ.filter fun i => Q.row i ≠ 0

def nonzeroColumns (Q : Matrix (Fin n) (Fin n) (ZMod 2)) : Finset (Fin n) :=
  Finset.univ.filter fun j => Q.col j ≠ 0

theorem nonzeroRows_eq_nonzeroColumns (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (hQ : Q.IsSymm) : nonzeroRows Q = nonzeroColumns Q := by
  ext j
  have hh : Q.row j = Q.col j := by
    funext i
    exact (congrArg (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => A j i)
      (show Q.transpose = Q from hQ)).symm
  simp only [nonzeroRows, nonzeroColumns, Finset.mem_filter, Finset.mem_univ, true_and, hh]

theorem nonzeroColumns_card_le_sparse_rank (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (w : ℕ)
    (hSparse : ∀ i, wordWeight (Q.row i) ≤ w) :
    (nonzeroColumns Q).card ≤ w * Q.rank := by
  classical
  obtain ⟨S, _, _, hsp, hind⟩ := exists_linearIndepOn_extension
    (K := ZMod 2) (v := Q.row) (s := (∅ : Set (Fin n))) (t := Set.univ)
    (linearIndepOn_empty (ZMod 2) Q.row) (Set.empty_subset _)
  have hspanS : Submodule.span (ZMod 2) (Q.row '' S) =
      Submodule.span (ZMod 2) (Q.row '' Set.univ) :=
    le_antisymm (Submodule.span_mono (Set.image_mono (Set.subset_univ S)))
      (Submodule.span_le.mpr hsp)
  letI : Fintype S := Fintype.ofFinite _
  let T := Set.toFinset S
  let supp (i : Fin n) := Finset.univ.filter fun j => Q i j ≠ 0
  have hr : T.card = Q.rank := by
    rw [Q.rank_eq_finrank_span_row]
    rw [show Set.range Q.row = Q.row '' (Set.univ : Set (Fin n)) by simp, ← hspanS]
    rw [← show Set.range (fun i : S => Q.row i.val) = Q.row '' S by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩]
    rw [finrank_span_eq_card hind]
    simp [T]
  have hcover : nonzeroColumns Q ⊆ T.biUnion supp := by
    intro j hj
    by_contra hnot
    let p : Submodule (ZMod 2) (BW n) :=
      (LinearMap.proj j : BW n →ₗ[ZMod 2] ZMod 2).ker
    have hp : Submodule.span (ZMod 2) (Q.row '' S) ≤ p := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hiS, rfl⟩
      change Q i j = 0
      by_contra hne
      exact hnot (Finset.mem_biUnion.mpr ⟨i, by simpa [T] using hiS,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩)
    have hh (i : Fin n) : Q i j = 0 := by
      have hi : Q.row i ∈ Submodule.span (ZMod 2) (Q.row '' S) := by
        rw [hspanS]
        exact Submodule.subset_span ⟨i, Set.mem_univ _, rfl⟩
      exact hp hi
    have hj' : Q.col j ≠ 0 := (Finset.mem_filter.mp hj).2
    exact hj' (funext hh)
  calc
    _ ≤ (T.biUnion supp).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ T, (supp i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ T, w := by
      apply Finset.sum_le_sum
      intro i _
      have hweight : wordWeight (Q.row i) ≤ w := hSparse i
      have hsupport : (supp i).card = wordWeight (Q.row i) := by
        unfold wordWeight
        congr 1
        exact @Finset.filter_congr_decidable _ Finset.univ (fun j => Q.row i j ≠ 0)
          (fun j => @instDecidableNot (Q.row i j = 0) (ZMod.decidableEq 2 (Q.row i j) 0))
          (fun j => @instDecidableNot (Q.row i j = 0) (Classical.propDecidable (Q.row i j = 0)))
      exact hsupport.trans_le hweight
    _ = w * Q.rank := by simp [hr, Nat.mul_comm]

abbrev plantedRestriction (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (p : BW n) :=
  Q.mulVecLin.comp (bitFunctional p).ker.subtype

abbrev plantedRank (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (p : BW n) :=
  Module.finrank (ZMod 2) (plantedRestriction Q p).range

theorem rank_le_plantedRank_add_one (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (p : BW n) :
    Q.rank ≤ plantedRank Q p + 1 := by
  let f := Q.mulVecLin
  let t := bitFunctional p
  let g := plantedRestriction Q p
  have hfo := f.finrank_range_add_finrank_ker
  have hgo := g.finrank_range_add_finrank_ker
  have hto := t.finrank_range_add_finrank_ker
  have htr : Module.finrank (ZMod 2) t.range ≤ 1 :=
    (Submodule.finrank_le _).trans (by simp)
  let j : g.ker →ₗ[ZMod 2] f.ker :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    have hv := congrArg (fun z : f.ker => z.val) he
    change x.val.val = y.val.val at hv
    exact Subtype.ext (Subtype.ext hv)
  have hker := LinearMap.finrank_le_finrank_of_injective (f := j) hj
  change Module.finrank (ZMod 2) f.range ≤ Module.finrank (ZMod 2) g.range + 1
  change Module.finrank (ZMod 2) g.range + Module.finrank (ZMod 2) g.ker =
    Module.finrank (ZMod 2) t.ker at hgo
  change Module.finrank (ZMod 2) f.range + Module.finrank (ZMod 2) f.ker =
    Module.finrank (ZMod 2) (BW n) at hfo
  omega

theorem plantedRestriction_ne_zero_of_sparse (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (p : BW n) (w : ℕ) (hQ : Q ≠ 0)
    (hSparse : ∀ i, wordWeight (Q.row i) ≤ w) (hWeight : w < wordWeight p) :
    plantedRestriction Q p ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, Q.row i ≠ 0 := by
    by_contra! h
    apply hQ
    ext i j
    exact congrFun (h i) j
  have hp : Q.row i ≠ p := fun he => (not_lt_of_ge (he ▸ hSparse i)) hWeight
  intro h
  apply bitFunctional_on_planted_nonzero p (Q.row i) hi hp
  ext x
  have hx := congrFun (LinearMap.congr_fun h x) i
  exact hx

/-- The manuscript's rank bound without division or rounding. -/
theorem nonzeroRows_card_le_twice_sparse_plantedRank
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (p : BW n) (w : ℕ)
    (hSymm : Q.IsSymm) (hQ : Q ≠ 0)
    (hSparse : ∀ i, wordWeight (Q.row i) ≤ w) (hWeight : w < wordWeight p) :
    (nonzeroRows Q).card ≤ 2 * w * plantedRank Q p := by
  have hrpos : 0 < plantedRank Q p := by
    by_contra! h
    have hz : (plantedRestriction Q p).range = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h)
    exact plantedRestriction_ne_zero_of_sparse Q p w hQ hSparse hWeight
      (LinearMap.range_eq_bot.mp hz)
  have hr : Q.rank ≤ 2 * plantedRank Q p :=
    (rank_le_plantedRank_add_one Q p).trans (by omega)
  rw [nonzeroRows_eq_nonzeroColumns Q hSymm]
  calc
    _ ≤ w * Q.rank := nonzeroColumns_card_le_sparse_rank Q w hSparse
    _ ≤ w * (2 * plantedRank Q p) := Nat.mul_le_mul_left _ hr
    _ = _ := by ring

#print axioms nonzeroColumns_card_le_sparse_rank
#print axioms rank_le_plantedRank_add_one
#print axioms plantedRestriction_ne_zero_of_sparse
#print axioms nonzeroRows_card_le_twice_sparse_plantedRank

end
end CriticalDepth.Manuscript20261114.CSSCheckSpaces
