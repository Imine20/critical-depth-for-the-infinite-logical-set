import CSSGeneratorFibers

/-!
Finite rank-deficiency counts for the symmetric sparse-matrix exclusion.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

variable {V W : Type*}
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]

theorem card_binaryColumns_in_subspace (S : Submodule (ZMod 2) W) (a : ℕ) :
    Nat.card {A : Fin a → W // ∀ i, A i ∈ S} = 2 ^ (a * Module.finrank (ZMod 2) S) := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  let f (A : {A : Fin a → W // ∀ i, A i ∈ S}) (i : Fin a) : S :=
    ⟨A.val i, A.property i⟩
  let g (A : Fin a → S) : {A : Fin a → W // ∀ i, A i ∈ S} :=
    ⟨fun i => (A i).val, fun i => (A i).property⟩
  let e : {A : Fin a → W // ∀ i, A i ∈ S} ≃ (Fin a → S) :=
    ⟨f, g, fun _ => rfl, fun A => funext fun i => Subtype.ext rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := S), ZMod.card, ← pow_mul, mul_comm]

/-- The column rank of a tuple is the dimension of the span of its columns. -/
noncomputable def columnFinrank (a : ℕ) (A : Fin a → W) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A))

theorem exists_containing_subspace_of_columnFinrank_le
    (a r : ℕ) (A : Fin a → W) (hA : columnFinrank a A ≤ r)
    (hr : r ≤ Module.finrank (ZMod 2) W) :
    ∃ S : Submodule (ZMod 2) W, Module.finrank (ZMod 2) S = r ∧ ∀ i, A i ∈ S := by
  let S := Submodule.span (ZMod 2) (Set.range A)
  have hS : Module.finrank (ZMod 2) S ≤ r := hA
  have extend (j : ℕ) (hj : Module.finrank (ZMod 2) S + j ≤ Module.finrank (ZMod 2) W) :
      ∃ T : Submodule (ZMod 2) W, S ≤ T ∧
        Module.finrank (ZMod 2) T = Module.finrank (ZMod 2) S + j := by
    induction j with
    | zero => exact ⟨S, le_rfl, by simp⟩
    | succ j ih =>
      obtain ⟨T, hST, hT⟩ := ih (by omega)
      obtain ⟨x, hx⟩ := T.exists_of_finrank_lt (by omega)
      refine ⟨T ⊔ Submodule.span (ZMod 2) {x}, hST.trans le_sup_left, ?_⟩
      have hx' : x ∉ T := by simpa using hx (1 : ZMod 2) one_ne_zero
      rw [Submodule.finrank_sup_span_singleton hx', hT]
      omega
  obtain ⟨T, hST, hT⟩ := extend (r - Module.finrank (ZMod 2) S) (by omega)
  exact ⟨T, by omega, fun i => hST (Submodule.subset_span ⟨i, rfl⟩)⟩

#print axioms card_binaryColumns_in_subspace
#print axioms exists_containing_subspace_of_columnFinrank_le

end CriticalDepth.Manuscript20261114.CSSCheckSpaces