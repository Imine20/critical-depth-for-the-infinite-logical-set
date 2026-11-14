import CSSFiniteColumns
import CSSCodeOrthogonality

/-!
Planting a minimum-weight dual word for the random X checks.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

variable {n : ℕ}
abbrev BW (n : ℕ) := Fin n → ZMod 2

def bitFunctional (x : BW n) : BW n →ₗ[ZMod 2] ZMod 2 := dotProductEquiv (ZMod 2) (Fin n) x

theorem bitFunctional_ker (x : BW n) :
    LinearMap.ker (bitFunctional x) = cssOrthogonal (Submodule.span (ZMod 2) {x}) := by
  ext y
  change dotProduct x y = 0 ↔ _
  rw [cssOrthogonal_mem]
  constructor
  · intro h z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [dotProduct_smul, dotProduct_comm, h, smul_zero]
  · intro h
    rw [dotProduct_comm]
    exact h x (Submodule.subset_span (by simp))

/-- On the planted hyperplane, every nonzero word different from the
planted word gives a nonzero evaluation functional. -/
theorem bitFunctional_on_planted_nonzero (p v : BW n) (hv : v ≠ 0) (hvp : v ≠ p) :
    (bitFunctional v).comp (LinearMap.ker (bitFunctional p)).subtype ≠ 0 := by
  intro h
  have hmem : v ∈ cssOrthogonal (cssOrthogonal (Submodule.span (ZMod 2) {p})) := by
    rw [cssOrthogonal_mem]
    intro x hx
    have hx' : x ∈ (bitFunctional p).ker := by rwa [bitFunctional_ker]
    exact LinearMap.congr_fun h (⟨x, hx'⟩ : (bitFunctional p).ker)
  rw [cssOrthogonal_involutive] at hmem
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
  rcases (show ∀ k : ZMod 2, k = 0 ∨ k = 1 by decide) k with e | e
  · exact hv (by simpa [e] using hk.symm)
  · exact hvp (by simpa [e] using hk.symm)

/-- The exact finite probability for an unexpected word in the dual of the
sampled column span. -/
theorem card_planted_columns_all_orthogonal (p v : BW n) (hv : v ≠ 0) (hvp : v ≠ p)
    (a : ℕ) :
    let V := (bitFunctional p).ker
    letI : Fintype V := Fintype.ofFinite _
    Nat.card {G : Fin a → V // ∀ i, dotProduct v (G i).val = 0} * 2 ^ a =
      (Fintype.card V) ^ a := by
  classical
  let V := (bitFunctional p).ker
  letI : Fintype V := Fintype.ofFinite _
  exact card_binary_columns_annihilated
    ((bitFunctional v).comp V.subtype) (bitFunctional_on_planted_nonzero p v hv hvp) a

#print axioms bitFunctional_on_planted_nonzero
#print axioms card_planted_columns_all_orthogonal

end CriticalDepth.Manuscript20261114.CSSCheckSpaces