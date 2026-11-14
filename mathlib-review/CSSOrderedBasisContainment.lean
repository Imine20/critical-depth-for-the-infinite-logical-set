import CSSOrderedBasisSampling
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Fintype.Powerset

/-!
Exact finite frequencies for containment under the uniform subspace law.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

local notation "𝔽" => ZMod 2

variable {V : Type*} [AddCommGroup V] [Module 𝔽 V] [Fintype V]

private theorem independent_iff_columnMap {s : ℕ} (G : Fin s → V) :
    LinearIndependent 𝔽 G ↔ Function.Injective (BinaryColumnMap G) := by
  rw [Fintype.linearIndependent_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  simp only [BinaryColumnMap, LinearEquiv.piRing_symm_apply, funext_iff, Pi.zero_apply]

/-- Number of ordered independent binary tuples in a finite vector space. -/
theorem card_fullRankBinaryColumns_product {s : ℕ} (hs : s ≤ Module.finrank 𝔽 V) :
    Nat.card (FullRankBinaryColumns V s) =
      ∏ i : Fin s, (2 ^ Module.finrank 𝔽 V - 2 ^ i.val) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun G => (independent_iff_columnMap G).symm)]
  simpa only [ZMod.card] using (card_linearIndependent (K := 𝔽) (V := V) hs)

private noncomputable def containingEquiv {b : ℕ} (T T' : Submodule 𝔽 V)
    (e : V ≃ₗ[𝔽] V) (h : T.map e.toLinearMap = T') :
    {S : BinarySubspacesOfDim V b // T ≤ S.val} ≃
      {S : BinarySubspacesOfDim V b // T' ≤ S.val} := by
  let E := Submodule.orderIsoMapComap e
  have hE (S : Submodule 𝔽 V) : Module.finrank 𝔽 (E S) = Module.finrank 𝔽 S :=
    (e.submoduleMap S).finrank_eq.symm
  have hE' (S : Submodule 𝔽 V) : Module.finrank 𝔽 (E.symm S) = Module.finrank 𝔽 S :=
    (hE (E.symm S)).symm.trans (congrArg (fun P : Submodule 𝔽 V => Module.finrank 𝔽 P)
      (E.apply_symm_apply S))
  have ht : E T = T' := h
  refine
    { toFun := fun S => ⟨⟨E S.val.val, (hE _).trans S.val.property⟩,
        ht ▸ E.monotone S.property⟩
      invFun := fun S => ⟨⟨E.symm S.val.val, (hE' _).trans S.val.property⟩,
        E.le_iff_le.mp (by simpa only [ht, E.apply_symm_apply] using S.property)⟩
      left_inv := fun S => Subtype.ext (Subtype.ext (E.symm_apply_apply S.val.val))
      right_inv := fun S => Subtype.ext (Subtype.ext (E.apply_symm_apply S.val.val)) }

/-- Uniform containment is independent of which subspace of the specified
dimension was prescribed. -/
theorem card_containing_binarySubspaces_eq {b : ℕ} {T T' : Submodule 𝔽 V}
    (hdim : Module.finrank 𝔽 T = Module.finrank 𝔽 T') :
    Nat.card {S : BinarySubspacesOfDim V b // T ≤ S.val} =
      Nat.card {S : BinarySubspacesOfDim V b // T' ≤ S.val} := by
  let e := LinearEquiv.ofFinrankEq T T' hdim
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hmap : T.map g.toLinearMap = T' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg ⟨y, hy⟩) ▸ (e ⟨y, hy⟩).property
    · intro hx
      let y := e.symm ⟨x, hx⟩
      refine ⟨y.val, y.property, ?_⟩
      exact (hg y).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  exact Nat.card_congr (containingEquiv T T' g hmap)

private noncomputable def subspaceColumnsEquiv {s : ℕ} (S : Submodule 𝔽 V) :
    {G : FullRankBinaryColumns V s // (BinaryColumnMap G.val).range ≤ S} ≃
      FullRankBinaryColumns S s := by
  let E := LinearEquiv.piRing 𝔽 V (Fin s) 𝔽
  let E' := LinearEquiv.piRing 𝔽 S (Fin s) 𝔽
  let toSubspace (G : {G : FullRankBinaryColumns V s // (BinaryColumnMap G.val).range ≤ S}) :=
    (BinaryColumnMap G.val.val).codRestrict S
      (fun x => G.property (LinearMap.mem_range_self (BinaryColumnMap G.val.val) x))
  refine
    { toFun := fun G => ⟨E' (toSubspace G), ?_⟩
      invFun := fun G => ⟨⟨E (S.subtype.comp (BinaryColumnMap G.val)), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change Function.Injective (E'.symm (E' (toSubspace G)))
    rw [E'.symm_apply_apply]
    exact fun x y h => G.val.property (congrArg (fun z : S => z.val) h)
  · change Function.Injective (E.symm (E (S.subtype.comp (BinaryColumnMap G.val))))
    rw [E.symm_apply_apply]
    exact Subtype.val_injective.comp G.property
  · change (E.symm (E (S.subtype.comp (BinaryColumnMap G.val)))).range ≤ S
    rw [E.symm_apply_apply]
    rintro _ ⟨x, rfl⟩
    exact ((BinaryColumnMap G.val) x).property
  · intro G
    apply Subtype.ext
    apply Subtype.ext
    change E (S.subtype.comp (E'.symm (E' (toSubspace G)))) = G.val.val
    rw [E'.symm_apply_apply]
    apply E.symm.injective
    rw [E.symm_apply_apply]
    exact LinearMap.ext fun x => rfl
  · intro G
    apply Subtype.ext
    apply E'.symm.injective
    rw [E'.symm_apply_apply]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (E.symm (E (S.subtype.comp (BinaryColumnMap G.val)))) x =
      ((BinaryColumnMap G.val) x).val
    rw [E.symm_apply_apply]
    rfl

/-- Count the incident pairs of an ordered independent tuple and a subspace.
After dividing by the full subspace count and the ambient tuple count, this
is the exact product for conditional containment. -/
theorem binarySubspace_containment_exact_frequency {b s : ℕ}
    (T : Submodule 𝔽 V) (hT : Module.finrank 𝔽 T = s) (hsb : s ≤ b) :
    Nat.card {S : BinarySubspacesOfDim V b // T ≤ S.val} *
        (∏ i : Fin s, (2 ^ Module.finrank 𝔽 V - 2 ^ i.val)) =
      Nat.card (BinarySubspacesOfDim V b) *
        (∏ i : Fin s, (2 ^ b - 2 ^ i.val)) := by
  classical
  let B := BinarySubspacesOfDim V b
  let A := FullRankBinaryColumns V s
  let F (S : B) := {G : A // (BinaryColumnMap G.val).range ≤ S.val}
  let J (G : A) := {S : B // (BinaryColumnMap G.val).range ≤ S.val}
  letI : Finite (Submodule 𝔽 V) := Finite.of_injective
    (fun P : Submodule 𝔽 V => (P : Set V)) SetLike.coe_injective
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype A := Fintype.ofFinite _
  let e : (Σ S : B, F S) ≃ (Σ G : A, J G) :=
    { toFun := fun x => ⟨x.2.val, x.1, x.2.property⟩
      invFun := fun x => ⟨x.2.val, x.1, x.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hF (S : B) : Nat.card (F S) = ∏ i : Fin s, (2 ^ b - 2 ^ i.val) := by
    letI : Fintype S.val := Fintype.ofFinite _
    calc
      Nat.card (F S) = Nat.card (FullRankBinaryColumns S.val s) :=
        Nat.card_congr (subspaceColumnsEquiv S.val)
      _ = _ := by
        have hs : s ≤ Module.finrank 𝔽 S.val := by rw [S.property]; exact hsb
        rw [card_fullRankBinaryColumns_product (V := S.val) hs, S.property]
  have hJ (G : A) : Nat.card (J G) = Nat.card {S : B // T ≤ S.val} := by
    apply card_containing_binarySubspaces_eq
    exact (fullRankBinaryColumnSpan G).property.trans hT.symm
  have hcard := Nat.card_congr e
  rw [Nat.card_sigma, Nat.card_sigma] at hcard
  simp only [hF, hJ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at hcard
  rw [← Nat.card_eq_fintype_card (α := B), ← Nat.card_eq_fintype_card (α := A)] at hcard
  have hs : s ≤ Module.finrank 𝔽 V := by rw [← hT]; exact Submodule.finrank_le T
  change Nat.card B * _ = Nat.card (FullRankBinaryColumns V s) * _ at hcard
  rw [card_fullRankBinaryColumns_product (V := V) hs] at hcard
  refine (Nat.mul_comm _ _).trans ?_
  exact hcard.symm

/-- Exact finite frequency of containing a prescribed nonzero word. -/
theorem binarySubspace_contains_word_exact_frequency {b : ℕ} (hb : 1 ≤ b)
    (v : V) (hv : v ≠ 0) :
    Nat.card {S : BinarySubspacesOfDim V b // v ∈ S.val} * (2 ^ Module.finrank 𝔽 V - 1) =
      Nat.card (BinarySubspacesOfDim V b) * (2 ^ b - 1) := by
  let T := Submodule.span 𝔽 ({v} : Set V)
  have hT : Module.finrank 𝔽 T = 1 := finrank_span_singleton hv
  have h := binarySubspace_containment_exact_frequency T hT hb
  let e : {S : BinarySubspacesOfDim V b // T ≤ S.val} ≃
      {S : BinarySubspacesOfDim V b // v ∈ S.val} :=
    Equiv.subtypeEquivRight (fun S => Submodule.span_singleton_le_iff_mem v S.val)
  rw [Nat.card_congr e] at h
  simpa using h

/-- Exact frequency of a uniform subspace lying inside a specified subspace.
This specializes to the event that a fixed functional annihilates the
uniform sample by taking `U` to be its kernel. -/
theorem binarySubspace_lies_in_exact_frequency {b : ℕ}
    (U : Submodule 𝔽 V) (hb : b ≤ Module.finrank 𝔽 U) :
    Nat.card {S : BinarySubspacesOfDim V b // S.val ≤ U} *
        (∏ i : Fin b, (2 ^ Module.finrank 𝔽 V - 2 ^ i.val)) =
      Nat.card (BinarySubspacesOfDim V b) *
        (∏ i : Fin b, (2 ^ Module.finrank 𝔽 U - 2 ^ i.val)) := by
  letI : Fintype U := Fintype.ofFinite _
  have he := binaryColumnSpan_event_exact_frequency
    (V := V) (b := b) (fun S => S.val ≤ U)
  change Nat.card {G : FullRankBinaryColumns V b // (BinaryColumnMap G.val).range ≤ U} *
      Nat.card (BinarySubspacesOfDim V b) = _ at he
  rw [Nat.card_congr (subspaceColumnsEquiv U), card_fullRankBinaryColumns_product hb,
    card_fullRankBinaryColumns_product (V := V) (hb.trans (Submodule.finrank_le U))] at he
  simpa only [mul_comm] using he.symm


#print axioms card_fullRankBinaryColumns_product
#print axioms binarySubspace_containment_exact_frequency
#print axioms binarySubspace_contains_word_exact_frequency
#print axioms binarySubspace_lies_in_exact_frequency

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
