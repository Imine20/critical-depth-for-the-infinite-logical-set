import CriticalDepthMathlib
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Coordinate projections of CSS check spaces

A projection failing to be surjective supplies a nonzero word of the dual
check space supported entirely on the selected coordinates. Consequently a
dual-distance bound ensures that every short prescribed bit pattern extends.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

noncomputable section

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Restriction to the selected coordinates. -/
def coordinateRestriction (S : Finset ι) : (ι → F) →ₗ[F] (S → F) where
  toFun x i := x i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coordinateRestriction_apply (S : Finset ι) (x : ι → F) (i : S) :
    coordinateRestriction S x i = x i.val := rfl

omit [Fintype ι] in
theorem coordinateRestriction_surjective (S : Finset ι) :
    Function.Surjective (coordinateRestriction (F := F) S) := by
  intro x
  refine ⟨fun i => if h : i ∈ S then x ⟨i, h⟩ else 0, ?_⟩
  funext i
  simp [i.property]

/-- The coordinate projection of a check subspace is onto if the dual has
no nonzero word supported within the selected coordinates. -/
theorem projection_surjective_of_no_supported_dual
    (H : Submodule F (ι → F)) (S : Finset ι)
    (hdual : ∀ w : ι → F, (∀ x ∈ H, dotProduct w x = 0) →
      (∀ i ∉ S, w i = 0) → w = 0) :
    Function.Surjective ((coordinateRestriction S).comp H.subtype) := by
  classical
  let R := coordinateRestriction (F := F) S
  let f := R.comp H.subtype
  change Function.Surjective f
  by_contra hnot
  have hlt : LinearMap.range f < ⊤ := lt_top_iff_ne_top.mpr fun h =>
    hnot (LinearMap.range_eq_top.mp h)
  obtain ⟨φ, hφ, hAnn⟩ := (LinearMap.range f).exists_le_ker_of_lt_top hlt
  let w : ι → F := (dotProductEquiv F ι).symm (φ.comp R)
  have hw (x : ι → F) : dotProduct w x = φ (R x) := by
    change dotProductEquiv F ι w x = (φ.comp R) x
    rw [(dotProductEquiv F ι).apply_symm_apply]
  have hwH (x : ι → F) (hx : x ∈ H) : dotProduct w x = 0 := by
    rw [hw]
    exact LinearMap.mem_ker.mp (hAnn ⟨⟨x, hx⟩, rfl⟩)
  have hwSupport (j : ι) (hj : j ∉ S) : w j = 0 := by
    have hbit : R (Pi.single j (1 : F)) = 0 := by
      funext i
      have hij : i.val ≠ j := fun h => hj (h ▸ i.property)
      simp [R, Pi.single_eq_of_ne hij]
    rw [← dotProduct_single_one w j, hw, hbit, map_zero]
  have hw0 := hdual w hwH hwSupport
  apply hφ
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := coordinateRestriction_surjective (F := F) S y
  rw [← show dotProduct w x = φ (coordinateRestriction S x) from hw x, hw0]
  simp

/-- The Hamming weight of a word in finite coordinates. -/
def wordWeight (w : ι → F) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => w i ≠ 0).card

theorem wordWeight_le_of_supported {w : ι → F} {S : Finset ι}
    (hw : ∀ i ∉ S, w i = 0) : wordWeight w ≤ S.card := by
  classical
  unfold wordWeight
  apply Finset.card_le_card
  intro i hi
  by_contra hnot
  exact (Finset.mem_filter.mp hi).2 (hw i hnot)

/-- Any pattern on fewer sites than the dual distance of a check space
can be extended to a word of the check space. -/
theorem exists_word_of_dual_distance
    (H : Submodule F (ι → F)) (S : Finset ι) (d : ℕ) (hSd : S.card < d)
    (hd : ∀ w : ι → F, w ≠ 0 → (∀ x ∈ H, dotProduct w x = 0) → d ≤ wordWeight w)
    (y : S → F) : ∃ x ∈ H, ∀ i : S, x i.val = y i := by
  have hsurj := projection_surjective_of_no_supported_dual H S (fun w hw hSupp => by
    by_contra hw0
    exact (not_le_of_gt hSd) ((hd w hw0 hw).trans (wordWeight_le_of_supported hSupp)))
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x.val, x.property, fun i => congrFun hx i⟩

section SparseSolutions

variable {b : ℕ} (B : Matrix (Fin b) ι F) (T : Finset ι)

/-- A full-row-rank matrix continues to span its codomain after deleting
coordinates if no nonzero row combination is supported on the deleted sites. -/
theorem remaining_columns_span
    (hRows : Function.Injective (fun a : Fin b → F => a ᵥ* B))
    (hdual : ∀ w : ι → F, w ≠ 0 → (∃ a : Fin b → F, a ᵥ* B = w) →
      T.card < wordWeight w) :
    Submodule.span F ((fun i => fun j => B j i) '' {i | i ∉ T}) = ⊤ := by
  classical
  let V := fun i => fun j => B j i
  let H := Submodule.span F (V '' {i | i ∉ T})
  change H = ⊤
  by_contra hnot
  obtain ⟨φ, hφ, hAnn⟩ := H.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hnot)
  let a : Fin b → F := (dotProductEquiv F (Fin b)).symm φ
  have ha (v : Fin b → F) : dotProduct a v = φ v := by
    change dotProductEquiv F (Fin b) a v = φ v
    rw [(dotProductEquiv F (Fin b)).apply_symm_apply]
  let w := a ᵥ* B
  have hSupp (i : ι) (hi : i ∉ T) : w i = 0 := by
    change dotProduct a (V i) = 0
    rw [ha]
    exact LinearMap.mem_ker.mp (hAnn (Submodule.subset_span ⟨i, hi, rfl⟩))
  have hw : w ≠ 0 := by
    intro hw
    have hz : a = 0 := hRows (hw.trans (Matrix.zero_vecMul B).symm)
    apply hφ
    apply LinearMap.ext
    intro v
    simpa only [← ha, hz, zero_dotProduct, LinearMap.zero_apply]
  exact (not_lt_of_ge (wordWeight_le_of_supported hSupp)) (hdual w hw ⟨a, rfl⟩)

/-- A linear combination of columns can be chosen with support of cardinality
at most the number of rows and avoiding every deleted column. -/
theorem exists_sparse_column_solution
    (hSpan : Submodule.span F ((fun i => fun j => B j i) '' {i | i ∉ T}) = ⊤)
    (y : Fin b → F) :
    ∃ x : ι → F, (∀ i ∈ T, x i = 0) ∧ wordWeight x ≤ b ∧ B *ᵥ x = y := by
  classical
  let v : ι → Fin b → F := fun i j => B j i
  obtain ⟨S, hST, _, hspanS, hind⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty F v) (Set.empty_subset {i | i ∉ T})
  let : Fintype S := (Set.toFinite S).fintype
  have hSsize : Fintype.card S ≤ b := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      using (LinearIndependent.fintype_card_le_finrank hind)
  have hS : y ∈ Submodule.span F (Set.range (fun i : S => v i.val)) := by
    rw [show Set.range (fun i : S => v i.val) = v '' S by ext; simp [Set.mem_image, Set.mem_range]]
    apply (Submodule.span_le.mpr hspanS : Submodule.span F (v '' {i | i ∉ T}) ≤ _)
    rw [hSpan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hS
  let x : ι → F := ∑ i : S, Pi.single i.val (c i)
  have hx (i : ι) (hi : i ∉ S) : x i = 0 := by
    change (∑ j : S, (Pi.single j.val (c j) : ι → F)) i = 0
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    have hne : i ≠ j.val := fun h => hi (h.symm ▸ j.property)
    exact Pi.single_eq_of_ne hne _
  have hxWeight : wordWeight x ≤ b := by
    have hw := wordWeight_le_of_supported (S := (Set.toFinite S).toFinset)
      (w := x) (fun i hi => hx i (by simpa using hi))
    exact hw.trans (by rwa [Set.Finite.card_toFinset])
  refine ⟨x, fun i hi => hx i (fun his => hST his hi), hxWeight, ?_⟩
  change B.mulVecLin x = y
  rw [show x = ∑ i : S, Pi.single i.val (c i) from rfl, map_sum, ← hc]
  apply Finset.sum_congr rfl
  intro i _
  ext j
  simp [v, Matrix.mulVec_single, smul_eq_mul, mul_comm]

/-- Extend one specified site to a kernel word by using at most b additional
sites, all outside the forbidden set. -/
theorem exists_sparse_kernel_word (B : Matrix (Fin b) ι F) (T : Finset ι)
    (hRows : Function.Injective (fun a : Fin b → F => a ᵥ* B))
    (hdual : ∀ w : ι → F, w ≠ 0 → (∃ a : Fin b → F, a ᵥ* B = w) →
      T.card < wordWeight w)
    (i : ι) (hi : i ∈ T) :
    ∃ a : ι → F, (∀ j ∈ T, a j = 0) ∧ wordWeight a ≤ b ∧
      B *ᵥ (Pi.single i 1 + a) = 0 ∧ ((Pi.single i (1 : F) : ι → F) + a) i = 1 := by
  obtain ⟨a, ha, hWeight, hSyndrome⟩ :=
    exists_sparse_column_solution B T (remaining_columns_span B T hRows hdual)
      (-(B *ᵥ Pi.single i 1))
  refine ⟨a, ha, hWeight, ?_, ?_⟩
  · rw [Matrix.mulVec_add, hSyndrome, add_neg_cancel]
  · simp [ha i hi]

end SparseSolutions

end

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
