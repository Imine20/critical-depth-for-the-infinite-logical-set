import CSSPermutationRigidity
import CSSCodeOrthogonality

/-!
# Short spanning words in the binary dual of a check space

For each column outside an independent spanning subset, express that
column using the subset. The resulting dependency word uses at most
one more site than the check-space dimension and these words span the
entire kernel.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript20261114.CSSCheckSpaces

variable {n : ℕ}

private theorem sum_column_additions {a : ℕ} (B : Matrix (Fin a) (Fin n) CSSBit)
    (v : CSSWord n) :
    B *ᵥ v = ∑ i, v i • (fun j => B j i) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The kernel of a binary a by n matrix is spanned by words of weight
at most a+1. No full rank assumption on the checks is needed. -/
theorem span_short_kernel_words {a : ℕ} (B : Matrix (Fin a) (Fin n) CSSBit) :
    Submodule.span CSSBit {v : CSSWord n | B *ᵥ v = 0 ∧ wordWeight v ≤ a + 1} =
      B.mulVecLin.ker := by
  classical
  let column (i : Fin n) : Fin a → CSSBit := fun j => B j i
  obtain ⟨P, _, _, hspan, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty CSSBit column) (Set.empty_subset (Set.univ : Set (Fin n)))
  let : Fintype P := (Set.toFinite P).fintype
  let sites := (Set.toFinite P).toFinset
  have hPcard : sites.card ≤ a := by
    rw [Set.Finite.card_toFinset]
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearIndependent.fintype_card_le_finrank hli
  have hBi (i : Fin n) : B *ᵥ (Pi.single i (1 : CSSBit) : CSSWord n) = column i := by
    funext j
    change dotProduct (B j) (Pi.single i 1) = B j i
    exact dotProduct_single_one (B j) i
  have hColumn (i : Fin n) :
      column i ∈ Submodule.span CSSBit (Set.range (fun j : P => column j.val)) := by
    have hImg : Set.range (fun j : P => column j.val) = column '' P := by
      ext j
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k.val, k.property, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, rfl⟩
    rw [hImg]
    exact hspan ⟨i, Set.mem_univ _, rfl⟩
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun CSSBit).mp (hColumn i)
  let dep (i : Fin n) : CSSWord n :=
    Pi.single i 1 - ∑ j : P, Pi.single j.val (c i j)
  have hDepKer (i : Fin n) : B *ᵥ dep i = 0 := by
    change B.mulVecLin (Pi.single i 1 - ∑ j : P, (Pi.single j.val (c i j) : CSSWord n)) = 0
    rw [map_sub, map_sum]
    change B *ᵥ Pi.single i 1 - ∑ j : P, B *ᵥ Pi.single j.val (c i j) = 0
    rw [hBi, ← hc i]
    apply sub_eq_zero.mpr
    apply Finset.sum_congr rfl
    intro j _
    funext t
    change c i j * column j.val t = dotProduct (B t) (Pi.single j.val (c i j))
    rw [dotProduct_single]
    exact mul_comm _ _
  have hDepWeight (i : Fin n) : wordWeight (dep i) ≤ a + 1 := by
    have hSupp : ∀ j ∉ insert i sites, dep i j = 0 := by
      intro j hj
      have hji : j ≠ i := fun he => hj (Finset.mem_insert.mpr (Or.inl he))
      have hjP : j ∉ P := by
        intro hjp
        exact hj (Finset.mem_insert_of_mem (by simpa [sites] using hjp))
      change (Pi.single i (1 : CSSBit) : CSSWord n) j -
        (∑ k : P, (Pi.single k.val (c i k) : CSSWord n)) j = 0
      rw [Finset.sum_apply, Pi.single_eq_of_ne hji]
      simp only [zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro k _
      have hne : j ≠ k.val := fun he => hjP (he.symm ▸ k.property)
      exact Pi.single_eq_of_ne hne _
    exact (wordWeight_le_of_supported hSupp).trans
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hPcard 1))
  let T := Submodule.span CSSBit {v : CSSWord n | B *ᵥ v = 0 ∧ wordWeight v ≤ a + 1}
  have hT : T ≤ B.mulVecLin.ker := Submodule.span_le.mpr fun v hv => hv.1
  apply le_antisymm hT
  intro v hv
  let w : CSSWord n := ∑ i ∈ Finset.univ \ sites, v i • dep i
  have hw : w ∈ T :=
    Submodule.sum_mem T fun i _ =>
      Submodule.smul_mem T _ (Submodule.subset_span ⟨hDepKer i, hDepWeight i⟩)
  have hsub : v - w ∈ B.mulVecLin.ker := Submodule.sub_mem _ hv (hT hw)
  have hOff (i : Fin n) (hi : i ∉ P) : (v - w) i = 0 := by
    have his : i ∈ Finset.univ \ sites := by simp [sites, hi]
    change v i - (∑ j ∈ Finset.univ \ sites, v j • dep j) i = 0
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem i his]
    · have hsum (j : Fin n) : dep j i = (Pi.single j (1 : CSSBit) : CSSWord n) i := by
        change _ - (∑ k : P, (Pi.single k.val (c j k) : CSSWord n)) i = _
        rw [Finset.sum_apply, Finset.sum_eq_zero]
        · rw [sub_zero]
        · intro k _
          exact Pi.single_eq_of_ne (fun hEq : i = k.val => hi (hEq.symm ▸ k.property)) _
      rw [Pi.smul_apply, hsum, Pi.single_eq_same, smul_eq_mul, mul_one, sub_self]
    · intro j _ hji
      change v j * dep j i = 0
      have hsum : (∑ k : P, (Pi.single k.val (c j k) : CSSWord n)) i = 0 := by
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro k _
        exact Pi.single_eq_of_ne (fun hEq : i = k.val => hi (hEq.symm ▸ k.property)) _
      have hh : dep j i = 0 := by
        change (Pi.single j (1 : CSSBit) : CSSWord n) i - _ = 0
        rw [Pi.single_eq_of_ne hji.symm, hsum, sub_zero]
      rw [hh, mul_zero]
  have hCoeff : ∀ j : P, (v - w) j.val = 0 := by
    have hEq : (∑ j : P, (v - w) j.val • column j.val) = 0 := by
      let e : P ≃ sites :=
        { toFun := fun j => ⟨j.val, by simpa [sites] using j.property⟩
          invFun := fun j => ⟨j.val, by simpa [sites] using j.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      calc
        _ = ∑ j : sites, (v - w) j.val • column j.val :=
          e.sum_comp (fun j => (v - w) j.val • column j.val)
        _ = ∑ j ∈ sites, (v - w) j • column j :=
          Finset.sum_coe_sort sites (fun j : Fin n => (v - w) j • column j)
        _ = ∑ j : Fin n, (v - w) j • column j := by
          apply Finset.sum_subset (Finset.subset_univ sites)
          intro i _ hi
          rw [hOff i (by simpa [sites] using hi), zero_smul]
        _ = 0 := by
          rw [← sum_column_additions]
          exact LinearMap.mem_ker.mp hsub
    intro j
    exact (linearIndependent_iff'.mp hli) Finset.univ (fun j : P => (v - w) j.val)
      hEq j (Finset.mem_univ j)
  have hzero : v - w = 0 := by
    funext i
    by_cases hi : i ∈ P
    · exact hCoeff ⟨i, hi⟩
    · exact hOff i hi
  exact sub_eq_zero.mp hzero ▸ hw

/-- The orthogonal complement of H is spanned by words of length at
most the number of independent X checks plus one. -/
theorem span_short_cssOrthogonal_words (H : Submodule CSSBit (CSSWord n)) :
    Submodule.span CSSBit {v : CSSWord n | v ∈ cssOrthogonal H ∧
      wordWeight v ≤ Module.finrank CSSBit H + 1} = cssOrthogonal H := by
  classical
  let b := Module.finBasis CSSBit H
  let B : Matrix (Fin (Module.finrank CSSBit H)) (Fin n) CSSBit := fun j i => (b j).val i
  have hker (v : CSSWord n) : B *ᵥ v = 0 ↔ v ∈ cssOrthogonal H := by
    constructor
    · intro hv x hx
      let y : H := ⟨x, hx⟩
      have hb : (∑ j, b.repr y j • (b j).val) = x := by
        have hh := congrArg Subtype.val (b.sum_repr y)
        simpa only [Submodule.coe_sum, SetLike.val_smul] using hh
      rw [← hb, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro j _
      have h := congrFun hv j
      change dotProduct (b j).val v = 0 at h
      rw [dotProduct_smul, dotProduct_comm v, h, smul_zero]
    · intro hv
      funext j
      change dotProduct (b j).val v = 0
      rw [dotProduct_comm]
      exact hv _ (b j).property
  have hset : {v : CSSWord n | B *ᵥ v = 0 ∧ wordWeight v ≤ Module.finrank CSSBit H + 1} =
      {v : CSSWord n | v ∈ cssOrthogonal H ∧ wordWeight v ≤ Module.finrank CSSBit H + 1} := by
    ext v
    exact and_congr_left' (hker v)
  rw [← hset, span_short_kernel_words B]
  ext v
  exact hker v

/-- The set of all short dual words gives a family of short
orthogonality tests of precisely the size bound used in the manuscript. -/
noncomputable def cssShortOrthogonalityTests
    (H : Submodule CSSBit (CSSWord n)) :
    ShortOrthogonalityTests H (Module.finrank CSSBit H + 1) where
  tests := {v | v ∈ cssOrthogonal H ∧ wordWeight v ≤ Module.finrank CSSBit H + 1}
  weight_le := fun _ hv => hv.2
  characterize := by
    intro x
    constructor
    · intro hx v hv
      exact hv.1 x hx
    · intro hx
      have hAll : ∀ v ∈ cssOrthogonal H, dotProduct v x = 0 := by
        rw [← span_short_cssOrthogonal_words H]
        have hker : Submodule.span CSSBit {v : CSSWord n | v ∈ cssOrthogonal H ∧
            wordWeight v ≤ Module.finrank CSSBit H + 1} ≤
            (dotProductEquiv CSSBit (Fin n) x).ker := by
          apply Submodule.span_le.mpr
          intro v hv
          apply LinearMap.mem_ker.mpr
          change dotProduct x v = 0
          rw [dotProduct_comm]
          exact hx v hv
        intro v hv
        have h := LinearMap.mem_ker.mp (hker hv)
        change dotProduct x v = 0 at h
        rw [dotProduct_comm]
        exact h
      rw [← cssOrthogonal_involutive H]
      intro v hv
      rw [dotProduct_comm]
      exact hAll v hv

#print axioms span_short_kernel_words
#print axioms span_short_cssOrthogonal_words
#print axioms cssShortOrthogonalityTests

end CriticalDepth.Manuscript20261114.CSSCode
