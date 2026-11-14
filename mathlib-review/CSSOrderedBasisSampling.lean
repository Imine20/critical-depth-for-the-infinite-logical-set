import CSSRestrictionFibers



/-!
The span of uniform ordered columns, conditioned on full column rank,
is uniform on the subspaces of that dimension.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

local notation "𝔽" => ZMod 2

universe u

variable {V : Type u} [AddCommGroup V] [Module 𝔽 V] [Fintype V]

abbrev BinaryColumnMap {b : ℕ} (G : Fin b → V) :
    (Fin b → 𝔽) →ₗ[𝔽] V :=
  (LinearEquiv.piRing 𝔽 V (Fin b) 𝔽).symm G

abbrev FullRankBinaryColumns (V : Type*) [AddCommGroup V] [Module 𝔽 V] (b : ℕ) :=
  {G : Fin b → V // Function.Injective (BinaryColumnMap G)}

abbrev BinarySubspacesOfDim (V : Type*) [AddCommGroup V] [Module 𝔽 V] (b : ℕ) :=
  {S : Submodule 𝔽 V // Module.finrank 𝔽 S = b}

abbrev BinaryBasisChanges (b : ℕ) := (Fin b → 𝔽) ≃ₗ[𝔽] (Fin b → 𝔽)

noncomputable def fullRankBinaryColumnSpan {b : ℕ}
    (G : FullRankBinaryColumns V b) : BinarySubspacesOfDim V b :=
  ⟨(BinaryColumnMap G.val).range, by
    rw [← (LinearEquiv.ofInjective (BinaryColumnMap G.val) G.property).finrank_eq]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]⟩

private theorem dim_finrank {b : ℕ} {G : Fin b → V}
    (hG : Module.finrank 𝔽 (BinaryColumnMap G).range = b) :
    Function.Injective (BinaryColumnMap G) := by
  have hs : Function.Surjective (BinaryColumnMap G).rangeRestrict := by
    intro z
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp z.property
    exact ⟨x, Subtype.ext hx⟩
  have heq : Module.finrank 𝔽 (Fin b → 𝔽) =
      Module.finrank 𝔽 (BinaryColumnMap G).range := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hG]
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hs
  intro x y hxy
  exact hi (Subtype.ext hxy)

/-- Each full-rank span fiber is the space of linear coordinates for that
subspace. -/
noncomputable def binaryColumnSpanFiberEquiv {b : ℕ} (S : BinarySubspacesOfDim V b) :
    {G : FullRankBinaryColumns V b // fullRankBinaryColumnSpan G = S} ≃
      ((Fin b → 𝔽) ≃ₗ[𝔽] S.val) where
  toFun G := by
    let A := BinaryColumnMap G.val.val
    have hAS : A.range = S.val := congrArg Subtype.val G.property
    let f := A.codRestrict S.val (fun x => hAS ▸ LinearMap.mem_range_self A x)
    refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
    · intro x y h
      exact G.val.property (congrArg Subtype.val h)
    · intro s
      have hmem : s.val ∈ A.range := hAS.symm ▸ s.property
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hmem
      exact ⟨x, Subtype.ext hx⟩
  invFun e := by
    let A := S.val.subtype.comp e.toLinearMap
    let E := LinearEquiv.piRing 𝔽 V (Fin b) 𝔽
    have hA : A.range = S.val := by
      change (S.val.subtype.comp e.toLinearMap).range = S.val
      rw [LinearMap.range_comp, LinearMap.range_eq_top_of_surjective _ e.surjective,
        Submodule.map_top, Submodule.range_subtype]
    have hi : Function.Injective (BinaryColumnMap (E A)) := by
      change Function.Injective (E.symm (E A))
      rw [E.symm_apply_apply]
      exact Subtype.val_injective.comp e.injective
    refine ⟨⟨E A, hi⟩, Subtype.ext ?_⟩
    change (E.symm (E A)).range = S.val
    simpa only [E.symm_apply_apply] using hA
  left_inv G := by
    apply Subtype.ext
    apply Subtype.ext
    let E := LinearEquiv.piRing 𝔽 V (Fin b) 𝔽
    change E _ = G.val.val
    apply E.symm.injective
    rw [E.symm_apply_apply]
    exact LinearMap.ext fun _ => rfl
  right_inv e := by
    ext x
    let E := LinearEquiv.piRing 𝔽 V (Fin b) 𝔽
    change E.symm (E (S.val.subtype.comp e.toLinearMap)) x = (e x).val
    rw [E.symm_apply_apply]
    rfl

/-- Full rank is exactly the event that the span dimension equals the number
of sampled columns. -/
theorem injective_binaryColumnMap_iff_finrank {b : ℕ} (G : Fin b → V) :
    Function.Injective (BinaryColumnMap G) ↔ Module.finrank 𝔽 (BinaryColumnMap G).range = b :=
  ⟨fun h => (fullRankBinaryColumnSpan (⟨G, h⟩ : FullRankBinaryColumns V b)).property, dim_finrank⟩

private noncomputable def basisChangesEquiv {b : ℕ} (S : BinarySubspacesOfDim V b) :
    ((Fin b → 𝔽) ≃ₗ[𝔽] S.val) ≃ BinaryBasisChanges b := by
  let e := (Module.finBasisOfFinrankEq 𝔽 S.val S.property).equivFun
  exact
    { toFun := fun A => A.trans e
      invFun := fun B => B.trans e.symm
      left_inv := fun A => LinearEquiv.ext fun x => e.symm_apply_apply (A x)
      right_inv := fun B => LinearEquiv.ext fun x => e.apply_symm_apply (B x) }

/-- All full-rank fibers have the identical finite set of basis changes
as their coordinates. -/
theorem card_binaryColumnSpanFiber {b : ℕ} (S : BinarySubspacesOfDim V b) :
    Nat.card {G : FullRankBinaryColumns V b // fullRankBinaryColumnSpan G = S} =
      Nat.card (BinaryBasisChanges b) :=
  Nat.card_congr ((binaryColumnSpanFiberEquiv S).trans (basisChangesEquiv S))

/-- The count of any span event equals its subspace count times the common
number of ordered bases. This gives exact conditional uniformity. -/
theorem card_fullRankBinaryColumnSpan_event {b : ℕ} (P : BinarySubspacesOfDim V b → Prop) :
    Nat.card {G : FullRankBinaryColumns V b // P (fullRankBinaryColumnSpan G)} =
      Nat.card {S : BinarySubspacesOfDim V b // P S} * Nat.card (BinaryBasisChanges b) := by
  let f (G : {G : FullRankBinaryColumns V b // P (fullRankBinaryColumnSpan G)}) :
      {S : BinarySubspacesOfDim V b // P S} :=
    ⟨fullRankBinaryColumnSpan G.val, G.property⟩
  let fibers (S : {S : BinarySubspacesOfDim V b // P S}) :
      {G // f G = S} ≃ {G : FullRankBinaryColumns V b // fullRankBinaryColumnSpan G = S.val} :=
    { toFun := fun G => ⟨G.val.val, congrArg Subtype.val G.property⟩
      invFun := fun G =>
        ⟨⟨G.val, G.property.symm ▸ S.property⟩, Subtype.ext G.property⟩
      left_inv := fun G => Subtype.ext (Subtype.ext rfl)
      right_inv := fun G => Subtype.ext rfl }
  let e := (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv fun S =>
    (fibers S).trans ((binaryColumnSpanFiberEquiv S.val).trans (basisChangesEquiv S.val)))
  rw [Nat.card_congr e, Nat.card_prod]

theorem card_fullRankBinaryColumns {b : ℕ} :
    Nat.card (FullRankBinaryColumns V b) =
      Nat.card (BinarySubspacesOfDim V b) * Nat.card (BinaryBasisChanges b) := by
  let e (α : Type u) : {x : α // True} ≃ α :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, trivial⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }
  have h := card_fullRankBinaryColumnSpan_event (V := V) (b := b) (fun _ => True)
  rwa [Nat.card_congr (e (FullRankBinaryColumns V b)),
    Nat.card_congr (e (BinarySubspacesOfDim V b))] at h

/-- Conditioning the independent uniform column sample on full rank gives the
uniform subspace law, expressed without dividing by a possibly empty event. -/
theorem binaryColumnSpan_event_exact_frequency {b : ℕ} (P : BinarySubspacesOfDim V b → Prop) :
    Nat.card {G : FullRankBinaryColumns V b // P (fullRankBinaryColumnSpan G)} *
        Nat.card (BinarySubspacesOfDim V b) =
      Nat.card {S : BinarySubspacesOfDim V b // P S} *
        Nat.card (FullRankBinaryColumns V b) := by
  rw [card_fullRankBinaryColumnSpan_event, card_fullRankBinaryColumns]
  ac_rfl

#print axioms injective_binaryColumnMap_iff_finrank
#print axioms card_binaryColumnSpanFiber
#print axioms card_fullRankBinaryColumnSpan_event
#print axioms binaryColumnSpan_event_exact_frequency

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
