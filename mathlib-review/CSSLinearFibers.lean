import CSSFiniteCounts

/-!
Cardinality of a fiber of a surjective binary linear map.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

section
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]

theorem card_binary_surjective_fiber (F : V →ₗ[ZMod 2] W) (hF : Function.Surjective F) (y : W) :
    Nat.card {x : V // F x = y} * Fintype.card W = Fintype.card V := by
  obtain ⟨x₀, hx₀⟩ := hF y
  let f (x : {x : V // F x = y}) : F.ker :=
    ⟨x.val - x₀, by rw [LinearMap.mem_ker, map_sub, x.property, hx₀, sub_self]⟩
  let g (z : F.ker) : {x : V // F x = y} :=
    ⟨z.val + x₀, by rw [map_add, LinearMap.mem_ker.mp z.property, hx₀, zero_add]⟩
  let e : {x : V // F x = y} ≃ F.ker :=
    ⟨f, g, fun x => Subtype.ext (sub_add_cancel x.val x₀),
      fun z => Subtype.ext (add_sub_cancel_right z.val x₀)⟩
  have er : F.range = ⊤ := LinearMap.range_eq_top.mpr hF
  rw [Nat.card_congr e, ← card_binary_linearMap_ker_add_range F]
  congr 1
  rw [er, Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_eq_fintype_card]

end

#print axioms card_binary_surjective_fiber

end CriticalDepth.Manuscript20261114.CSSCheckSpaces