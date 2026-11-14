import CSSLinearFibers
import CSSPlantedHyperplane

/-!
Uniform images of random generator matrices.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

/-- Evaluation of a random matrix on a nonzero coefficient vector is
uniform on the column space from which the matrix was sampled. -/
theorem card_linearCombination_fiber {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (y : ι → ZMod 2) (i : ι) (hi : y i ≠ 0) (v : V) :
    Nat.card {A : ι → V // (∑ j, y j • A j) = v} =
      (Fintype.card V) ^ (Fintype.card ι - 1) := by
  classical
  have hi' : y i = 1 := by
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) (y i) with ho | ho
    · exact (hi ho).elim
    · exact ho
  let F := (LinearEquiv.piRing (ZMod 2) V ι (ZMod 2)).symm
  let L : (ι → V) →ₗ[ZMod 2] V :=
    (LinearMap.applyₗ' (ZMod 2) y).comp F.toLinearMap
  have hs : Function.Surjective L := by
    intro z
    refine ⟨Pi.single i z, ?_⟩
    change F (Pi.single i z) y = z
    rw [LinearEquiv.piRing_symm_apply]
    rw [Finset.sum_eq_single i]
    · simp [hi']
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have he (A : ι → V) : L A = ∑ j, y j • A j := by
    change F A y = _
    simp only [F, LinearEquiv.piRing_symm_apply]
  let E : {x : ι → V // L x = v} ≃ {x : ι → V // (∑ j, y j • x j) = v} :=
    Equiv.subtypeEquivRight (fun x => by rw [he])
  have hc := card_binary_surjective_fiber L hs v
  rw [Nat.card_congr E] at hc
  rw [Fintype.card_fun] at hc
  have hi₀ := Fintype.card_pos_iff.mpr (show Nonempty ι from ⟨i⟩)
  have hV := Fintype.card_pos_iff.mpr (show Nonempty V from ⟨0⟩)
  have hpow : Fintype.card V ^ Fintype.card ι =
      Fintype.card V ^ (Fintype.card ι - 1) * Fintype.card V := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow] at hc
  exact Nat.eq_of_mul_eq_mul_right hV hc

#print axioms card_linearCombination_fiber

end CriticalDepth.Manuscript20261114.CSSCheckSpaces