import CSSFiniteCounts

/-!
Independent sampling of constrained binary columns.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

/-- A nonzero linear binary functional onto the field has equally many
vectors of each value. The same coordinate condition in k independent
columns therefore reduces the sample space by an exact factor of 2^k. -/
theorem card_binary_columns_annihilated {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (F : V →ₗ[ZMod 2] ZMod 2) (hF : F ≠ 0) (k : ℕ) :
    Nat.card {A : Fin k → V // ∀ i, F (A i) = 0} * 2 ^ k = (Fintype.card V) ^ k := by
  classical
  have hsurj : Function.Surjective F := by
    have hex : ∃ v, F v ≠ 0 := by
      by_contra! h
      exact hF (LinearMap.ext h)
    obtain ⟨v, hv⟩ := hex
    have hval : F v = 1 := by
      rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) (F v) with h | h
      · exact (hv h).elim
      · exact h
    intro b
    exact ⟨b • v, by simp [map_smul, hval]⟩
  let V0 := F.ker
  let e : {A : Fin k → V // ∀ i, F (A i) = 0} ≃ (Fin k → ↥V0) :=
    { toFun := fun A i => ⟨A.val i, A.property i⟩
      invFun := fun A => ⟨fun i => (A i).val, fun i => (A i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun A => funext fun i => Subtype.ext rfl }
  have hr : Nat.card F.range = 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    exact (Nat.card_congr Submodule.topEquiv.toEquiv).trans (by simp [Nat.card_eq_fintype_card])
  have hnum := card_binary_linearMap_ker_add_range F
  rw [hr] at hnum
  letI : Fintype V0 := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← mul_pow]
  congr 1
  simpa [V0, Nat.card_eq_fintype_card] using hnum

#print axioms card_binary_columns_annihilated

end CriticalDepth.Manuscript20261114.CSSCheckSpaces