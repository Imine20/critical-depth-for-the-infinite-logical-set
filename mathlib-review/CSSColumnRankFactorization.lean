import CSSRestrictionFibers

/-!
Finite counts for low-rank random column families and containment in their span.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

local notation "𝔽" => ZMod 2
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V] [Fintype V]

theorem card_low_rank_binaryColumns_bound (a s : ℕ) (hs : s ≤ Module.finrank 𝔽 V) :
    Nat.card {G : Fin a → V // columnFinrank a G ≤ s} ≤
      2 ^ ((Module.finrank 𝔽 V + a) * s) := by
  classical
  let T := {G : Fin a → V // columnFinrank a G ≤ s}
  let D := (Fin s → V) × (Fin a → Fin s → 𝔽)
  let combine (z : D) (i : Fin a) : V := ∑ j, z.2 i j • z.1 j
  have hfactor (G : T) : ∃ z : D, combine z = G.val := by
    obtain ⟨S, hS, hG⟩ := exists_containing_subspace_of_columnFinrank_le
      a s G.val G.property hs
    let e := Module.finBasisOfFinrankEq 𝔽 S hS
    refine ⟨(fun j => (e j).val, fun i j => e.repr ⟨G.val i, hG i⟩ j), ?_⟩
    funext i
    simpa only [combine, Finsupp.sum_fintype, zero_smul, Submodule.coe_sum, Submodule.coe_smul]
      using congrArg (fun x : S => x.val) (e.sum_repr (⟨G.val i, hG i⟩ : S))
  choose factor hf using hfactor
  have hi : Function.Injective factor := fun x y e =>
    Subtype.ext ((hf x).symm.trans ((congrArg combine e).trans (hf y)))
  refine (Nat.card_le_card_of_injective factor hi).trans_eq ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Module.card_eq_pow_finrank (K := 𝔽) (V := V), ZMod.card, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

private theorem map_column_value {a : ℕ} (G : Fin a → V) (i : Fin a) :
    (LinearEquiv.piRing 𝔽 V (Fin a) 𝔽).symm G (Pi.single i 1) = G i := by
  have h := congrFun ((LinearEquiv.piRing 𝔽 V (Fin a) 𝔽).apply_symm_apply G) i
  exact h

/-- At most one fiber bound for each possible injective coefficient tuple
lifting an ordered basis of the prescribed subspace. -/
theorem card_binaryColumns_containing_le (a s : ℕ) (L : Submodule 𝔽 V)
    (hL : Module.finrank 𝔽 L = s) :
    Nat.card {G : Fin a → V // L ≤ ((LinearEquiv.piRing 𝔽 V (Fin a) 𝔽).symm G).range} *
      Fintype.card V ^ s ≤ 2 ^ (a * s) * Fintype.card V ^ a := by
  classical
  let E := LinearEquiv.piRing 𝔽 V (Fin a) 𝔽
  let D := (Fin s → 𝔽) →ₗ[𝔽] (Fin a → 𝔽)
  let E₀ := LinearEquiv.piRing 𝔽 (Fin a → 𝔽) (Fin s) 𝔽
  letI : Fintype D := Fintype.ofEquiv (Fin s → Fin a → 𝔽) E₀.symm.toEquiv
  let b := Module.finBasisOfFinrankEq 𝔽 L hL
  let B (i : Fin s) : V := (b i).val
  let good := Finset.univ.filter fun G : Fin a → V => L ≤ (E.symm G).range
  let fiber (Y : D) : Finset (Fin a → V) := Finset.univ.filter fun G =>
    Function.Injective Y ∧ ∀ i, (∑ j, Y (Pi.single i 1) j • G j) = B i
  have hsub : good ⊆ (Finset.univ : Finset D).biUnion fiber := by
    intro G hG
    have hInc := (Finset.mem_filter.mp hG).2
    have hB (i : Fin s) : B i ∈ (E.symm G).range := hInc (b i).property
    choose y hy using fun i => LinearMap.mem_range.mp (hB i)
    let Y : D := (LinearEquiv.piRing 𝔽 (Fin a → 𝔽) (Fin s) 𝔽).symm y
    let W : (Fin s → 𝔽) →ₗ[𝔽] V := L.subtype.comp b.equivFun.symm.toLinearMap
    have hW : Function.Injective W := Subtype.val_injective.comp b.equivFun.symm.injective
    have hcomp : (E.symm G).comp Y = W := by
      apply (LinearEquiv.piRing 𝔽 V (Fin s) 𝔽).injective
      funext i
      rw [LinearEquiv.piRing_apply, LinearEquiv.piRing_apply, LinearMap.comp_apply]
      rw [map_column_value, hy]
      change B i = (b.equivFun.symm (Pi.single i 1)).val
      have hb : b.equivFun (b i) = (Pi.single i 1 : Fin s → 𝔽) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp
        · simp [hj, Ne.symm hj]
      rw [← hb, LinearEquiv.symm_apply_apply]
    have hY : Function.Injective Y := fun x z h => hW (by
      rw [← hcomp, LinearMap.comp_apply, LinearMap.comp_apply, h])
    refine Finset.mem_biUnion.mpr ⟨Y, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY, ?_⟩⟩
    intro i
    have hk : (E.symm G) (Y (Pi.single i 1)) = B i := by
      rw [map_column_value]
      exact hy i
    simpa only [E, LinearEquiv.piRing_symm_apply] using hk
  have hf (Y : D) : (fiber Y).card * Fintype.card V ^ s ≤ Fintype.card V ^ a := by
    by_cases hY : Function.Injective Y
    · have h := card_binary_restriction_fiber Y hY B
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      simpa [fiber, hY] using h.le
    · simp [fiber, hY]
  have hcard : (Finset.univ : Finset D).card = 2 ^ (a * s) := by
    rw [Finset.card_univ, Fintype.card_congr (LinearEquiv.piRing 𝔽 (Fin a → 𝔽) (Fin s) 𝔽).toEquiv,
      Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card, ← pow_mul]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change good.card * Fintype.card V ^ s ≤ _
  calc
    _ ≤ ((Finset.univ : Finset D).biUnion fiber).card * Fintype.card V ^ s :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ Y : D, (fiber Y).card) * Fintype.card V ^ s :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ ≤ ∑ _Y : D, Fintype.card V ^ a := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun Y _ => hf Y
    _ = 2 ^ (a * s) * Fintype.card V ^ a := by
      rw [Finset.sum_const_nat (fun _ _ => rfl), hcard]

#print axioms card_low_rank_binaryColumns_bound
#print axioms card_binaryColumns_containing_le

end CriticalDepth.Manuscript20261114.CSSCheckSpaces