import CSSColumnRankCounts
import CSSLinearFibers

/-!
Uniform restriction of a binary linear map to a specified subspace.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators


section
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

local notation "𝔽" => ZMod 2

/-- An injective tuple of coefficients imposes exactly one independent word
equation for every column of the required restriction. -/
theorem card_binary_restriction_fiber {a s : ℕ}
    (Y : (Fin s → 𝔽) →ₗ[𝔽] (Fin a → 𝔽)) (hY : Function.Injective Y) (B : Fin s → V) :
    Nat.card {G : Fin a → V // ∀ i, (∑ j, Y (Pi.single i 1) j • G j) = B i} *
      Fintype.card V ^ s = Fintype.card V ^ a := by
  classical
  let Ea := LinearEquiv.piRing 𝔽 V (Fin a) 𝔽
  let Es := LinearEquiv.piRing 𝔽 V (Fin s) 𝔽
  let R₀ := LinearMap.lcomp 𝔽 V Y
  let R := Es.toLinearMap.comp (R₀.comp Ea.symm.toLinearMap)
  have ha (G : Fin a → V) (i : Fin s) : R G i = ∑ j, Y (Pi.single i 1) j • G j := by
    change Es ((Ea.symm G).comp Y) i = _
    simp [Ea, Es]
  obtain ⟨Z, hZ⟩ := Y.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hY)
  have hR : Function.Surjective R := by
    intro b
    refine ⟨Ea ((Es.symm b).comp Z), ?_⟩
    change Es ((Ea.symm (Ea ((Es.symm b).comp Z))).comp Y) = b
    rw [LinearEquiv.symm_apply_apply, LinearMap.comp_assoc, hZ, LinearMap.comp_id,
      LinearEquiv.apply_symm_apply]
  have hp (G : Fin a → V) : (∀ i, (∑ j, Y (Pi.single i 1) j • G j) = B i) ↔ R G = B := by
    rw [funext_iff]
    simp only [ha]
  let e : {G : Fin a → V // ∀ i, (∑ j, Y (Pi.single i 1) j • G j) = B i} ≃
      {G : Fin a → V // R G = B} :=
    Equiv.subtypeEquivRight hp
  rw [Nat.card_congr e]
  simpa only [Fintype.card_fun, Fintype.card_fin] using card_binary_surjective_fiber R hR B

end

#print axioms card_binary_restriction_fiber

end CriticalDepth.Manuscript20261114.CSSCheckSpaces