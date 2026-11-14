import CSSSparseSymmetricRank
import CSSColumnRankFactorization
import CSSRandomZChecks

/-!
The finite events for a fixed sparse symmetric matrix. Applying the matrix
to independent planted columns is uniform on its image. Containment in the
sampled Z-check span is counted in the same independent-column space.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

noncomputable section

variable {n a : ℕ}

set_option maxHeartbeats 300000 in
theorem card_binaryColumn_preimage
    {V W : Type*} [AddCommGroup V] [Module CSSBit V] [Fintype V]
    [AddCommGroup W] [Module CSSBit W] [Fintype W]
    (f : V →ₗ[CSSBit] W) (hf : Function.Surjective f) (a : ℕ)
    (P : (Fin a → W) → Prop) :
    Nat.card {G : Fin a → V // P (fun i => f (G i))} * (Fintype.card W) ^ a =
      Nat.card {B : Fin a → W // P B} * (Fintype.card V) ^ a := by
  classical
  let X := Fin a → V
  let Y := Fin a → W
  let F : X →ₗ[CSSBit] Y :=
    { toFun := fun G i => f (G i)
      map_add' := fun x y => funext fun i => f.map_add (x i) (y i)
      map_smul' := fun c x => funext fun i => f.map_smul c (x i) }
  have hF : Function.Surjective F := by
    intro B
    choose G hG using fun i => hf (B i)
    exact ⟨G, funext hG⟩
  let s : Finset X := Finset.univ.filter fun G => P (F G)
  let t : Finset Y := Finset.univ.filter P
  have hmaps : Set.MapsTo F (↑s : Set X) (↑t : Set Y) := by
    intro G hG
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hG).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (B : Y) (hB : B ∈ t) :
      (s.filter fun G => F G = B).card * (Fintype.card W) ^ a =
        (Fintype.card V) ^ a := by
    have he : (s.filter fun G => F G = B) = Finset.univ.filter fun G => F G = B := by
      ext G
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨h.symm ▸ (Finset.mem_filter.mp hB).2, h⟩⟩
    rw [he, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    have h := card_binary_surjective_fiber F hF B
    simpa only [X, Y, Fintype.card_fun, Fintype.card_fin] using h
  change Nat.card {G : X // P (F G)} * _ = Nat.card {B : Y // P B} * _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype]
  change s.card * _ = t.card * _
  rw [hcard, Finset.sum_mul]
  calc
    _ = ∑ _B ∈ t, (Fintype.card V) ^ a := Finset.sum_congr rfl hfiber
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-- The randomized columns of a fixed matrix after restricting its domain
to the planted hyperplane, with codomain its image. -/
abbrev plantedImageColumns (Q : Matrix (Fin n) (Fin n) CSSBit) (p : BW n)
    (G : Fin a → PlantedColumnSpace p) : Fin a → (plantedRestriction Q p).range :=
  fun i => (plantedRestriction Q p).rangeRestrict (G i)

theorem card_plantedQ_low_image_rank_bound
    (Q : Matrix (Fin n) (Fin n) CSSBit) (p : BW n)
    (a s : ℕ) (hs : s ≤ plantedRank Q p) :
    Nat.card {G : Fin a → PlantedColumnSpace p //
        columnFinrank a (plantedImageColumns Q p G) ≤ s} *
      2 ^ (plantedRank Q p * a) ≤
      2 ^ ((plantedRank Q p + a) * s) * Nat.card (Fin a → PlantedColumnSpace p) := by
  classical
  let V := PlantedColumnSpace p
  let W := (plantedRestriction Q p).range
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  have he := card_binaryColumn_preimage (plantedRestriction Q p).rangeRestrict
    (plantedRestriction Q p).surjective_rangeRestrict a (fun B => columnFinrank a B ≤ s)
  rw [Module.card_eq_pow_finrank (K := CSSBit) (V := W), ZMod.card, ← pow_mul] at he
  have h := card_low_rank_binaryColumns_bound (V := W) a s hs
  rw [Nat.card_eq_fintype_card (α := Fin a → V), Fintype.card_fun, Fintype.card_fin]
  exact he.le.trans (Nat.mul_le_mul_right _ h)

theorem range_piRing_eq_span_columns
    {V : Type*} [AddCommGroup V] [Module CSSBit V] (G : Fin a → V) :
    ((LinearEquiv.piRing CSSBit V (Fin a) CSSBit).symm G).range =
      Submodule.span CSSBit (Set.range G) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [LinearEquiv.piRing_symm_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    have h := congrFun ((LinearEquiv.piRing CSSBit V (Fin a) CSSBit).apply_symm_apply G) i
    exact h

theorem plantedImageColumns_finrank_eq
    (Q : Matrix (Fin n) (Fin n) CSSBit) (p : BW n) (G : Fin a → PlantedColumnSpace p) :
    columnFinrank a (plantedImageColumns Q p G) =
      Module.finrank CSSBit ((columnsToWord G).range.map Q.mulVecLin) := by
  let V := PlantedColumnSpace p
  let f := plantedRestriction Q p
  let M := (LinearEquiv.piRing CSSBit V (Fin a) CSSBit).symm G
  let B := (LinearEquiv.piRing CSSBit f.range (Fin a) CSSBit).symm
    (plantedImageColumns Q p G)
  have h₁ : B = f.rangeRestrict.comp M := by
    ext x
    simp only [B, M, LinearEquiv.piRing_symm_apply, LinearMap.comp_apply,
      map_sum, LinearMap.map_smul, plantedImageColumns, f]
  have h₂ : columnsToWord G = V.subtype.comp M := by
    apply LinearMap.ext
    intro x
    change (∑ i, x i • (G i).val) = ((M x : V) : BW n)
    simp only [M, LinearEquiv.piRing_symm_apply, Submodule.coe_sum, Submodule.coe_smul]
  have h₃ : B.range.map f.range.subtype = (columnsToWord G).range.map Q.mulVecLin := by
    rw [← LinearMap.range_comp, ← LinearMap.range_comp, h₁, h₂,
      ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, LinearMap.subtype_comp_rangeRestrict]
  have h₄ : columnFinrank a (plantedImageColumns Q p G) = Module.finrank CSSBit B.range := by
    change Module.finrank CSSBit _ = Module.finrank CSSBit B.range
    rw [range_piRing_eq_span_columns]
  rw [h₄, ← h₃]
  exact (f.range.equivSubtypeMap B.range).finrank_eq

/-- The prescribed ambient space may lie outside the sampling subspace.
In that case the containment event is empty. -/
theorem card_zSamples_containing_ambient_le
    (H L : Submodule CSSBit (BW n)) (b : ℕ) :
    Nat.card {G : Fin b → cssOrthogonal H // L ≤ (zColumnsToWord H G).range} *
        2 ^ (Module.finrank CSSBit (cssOrthogonal H) * Module.finrank CSSBit L) ≤
      2 ^ (b * Module.finrank CSSBit L) * Nat.card (Fin b → cssOrthogonal H) := by
  classical
  let V := cssOrthogonal H
  letI : Fintype V := Fintype.ofFinite _
  let T := {G : Fin b → V // L ≤ (zColumnsToWord H G).range}
  change Nat.card T * _ ≤ _
  by_cases hLV : L ≤ V
  · let L₀ := L.comap V.subtype
    let E := LinearEquiv.piRing CSSBit V (Fin b) CSSBit
    have hdim : Module.finrank CSSBit L₀ = Module.finrank CSSBit L :=
      (Submodule.comap_equiv_self_of_inj_of_le V.subtype_injective
        (by simpa only [Submodule.range_subtype] using hLV)).finrank_eq
    let j : T → {G : Fin b → V // L₀ ≤ (E.symm G).range} := fun G =>
      ⟨G.val, fun x hx => by
        have hm : x.val ∈ (zColumnsToWord H G.val).range := G.property hx
        obtain ⟨y, hy⟩ := hm
        exact ⟨y, Subtype.ext hy⟩⟩
    have hj : Function.Injective j := fun x y h =>
      Subtype.ext (congrArg (fun G : {G : Fin b → V // L₀ ≤ (E.symm G).range} => G.val) h)
    have h := card_binaryColumns_containing_le b (Module.finrank CSSBit L) L₀ hdim
    rw [Module.card_eq_pow_finrank (K := CSSBit) (V := V), ZMod.card, ← pow_mul, ← pow_mul] at h
    have htotal : Nat.card (Fin b → V) = 2 ^ (Module.finrank CSSBit V * b) := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := V), Nat.card_eq_fintype_card (α := Fin b),
        Fintype.card_fin, Module.card_eq_pow_finrank (K := CSSBit) (V := V), ZMod.card, ← pow_mul]
    rw [htotal]
    exact (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective j hj)).trans h
  · letI : IsEmpty T := ⟨fun G => hLV (G.property.trans (zColumnsToWord_range_le H G.val))⟩
    simp

#print axioms card_binaryColumn_preimage
#print axioms card_plantedQ_low_image_rank_bound
#print axioms plantedImageColumns_finrank_eq
#print axioms card_zSamples_containing_ambient_le

end
end CriticalDepth.Manuscript20261114.CSSCheckSpaces
