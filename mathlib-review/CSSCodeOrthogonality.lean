import CSSCheckSpaces
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Binary orthogonal spaces of CSS checks

The defining pairing is the same coordinate dot product used in the
projection and sparse-word lemmas.
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open Matrix
open scoped BigOperators

abbrev CSSBit := ZMod 2
abbrev CSSWord (n : ℕ) := Fin n → CSSBit

variable {n : ℕ}

/-- Binary orthogonality for a subspace of words in the physical coordinates. -/
def cssOrthogonal (S : Submodule CSSBit (CSSWord n)) : Submodule CSSBit (CSSWord n) where
  carrier := {x | ∀ z ∈ S, dotProduct x z = 0}
  zero_mem' := by
    intro z _
    simp [dotProduct]
  add_mem' := by
    intro x y hx hy z hz
    change dotProduct (x + y) z = 0
    have h : dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
      simp [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [h, hx z hz, hy z hz, add_zero]
  smul_mem' := by
    intro a x hx z hz
    change dotProduct (a • x) z = 0
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    change a * dotProduct x z = 0
    rw [hx z hz, mul_zero]

theorem cssOrthogonal_mem (S : Submodule CSSBit (CSSWord n)) (x : CSSWord n) :
    x ∈ cssOrthogonal S ↔ ∀ z ∈ S, dotProduct x z = 0 :=
  Iff.rfl

theorem cssChecksCompatible_symm {H J : Submodule CSSBit (CSSWord n)} :
    H ≤ cssOrthogonal J ↔ J ≤ cssOrthogonal H := by
  constructor <;> intro h x hx y hy <;> rw [dotProduct_comm] <;> exact h hy x hx

/-- A word outside a check subspace is detected by a dual word. -/
theorem exists_orthogonal_dot_one (S : Submodule CSSBit (CSSWord n)) (x : CSSWord n)
    (hx : x ∉ S) :
    ∃ z ∈ cssOrthogonal S, dotProduct z x = 1 := by
  let v : CSSWord n ⧸ S := Submodule.Quotient.mk x
  have hv : v ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero S).mp h)
  let U : Submodule CSSBit (CSSWord n ⧸ S) := Submodule.span CSSBit {v}
  have hi : Function.Injective (fun t : CSSBit => t • v) := by
    intro a b h
    change a • v = b • v at h
    have hh : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hh with hz | hz
    · exact sub_eq_zero.mp hz
    · exact (hv hz).elim
  let e : CSSBit ≃ₗ[CSSBit] U :=
    LinearEquiv.ofBijective
      { toFun := fun a => ⟨a • v, Submodule.mem_span_singleton.mpr ⟨a, rfl⟩⟩
        map_add' := fun a b => Subtype.ext (add_smul a b v)
        map_smul' := fun a b => Subtype.ext (mul_smul a b v) }
      ⟨fun _ _ h => hi (congrArg Subtype.val h), fun u => by
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp u.property
        exact ⟨a, Subtype.ext ha⟩⟩
  have he : e 1 = ⟨v, Submodule.subset_span (Set.mem_singleton v)⟩ := by
    apply Subtype.ext
    change (1 : CSSBit) • v = v
    exact one_smul _ _
  obtain ⟨V, hV⟩ := Submodule.exists_isCompl U
  let φ : (CSSWord n ⧸ S) →ₗ[CSSBit] CSSBit :=
    e.symm.toLinearMap.comp (Submodule.projectionOnto U V hV)
  have hφ : φ v = 1 := by
    rw [show v = ((e 1 : U) : CSSWord n ⧸ S) from by rw [he]]
    change e.symm (U.projectionOnto V hV (e 1 : U)) = 1
    have hp : U.projectionOnto V hV (e 1 : U) = e 1 := by
      first
      | exact U.projectionOnto_apply_left V hV (e 1)
      | exact?
    rw [hp, LinearEquiv.symm_apply_apply]
  let z := (dotProductEquiv CSSBit (Fin n)).symm (φ.comp S.mkQ)
  have hcomp (y : CSSWord n) : dotProduct z y = φ (S.mkQ y) := by
    change dotProductEquiv CSSBit (Fin n) z y = _
    rw [(dotProductEquiv CSSBit (Fin n)).apply_symm_apply]
    rfl
  refine ⟨z, ?_, ?_⟩
  · intro y hy
    rw [hcomp, show S.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero S).mpr hy, map_zero]
  · rw [hcomp]
    exact hφ

theorem cssOrthogonal_involutive (S : Submodule CSSBit (CSSWord n)) :
    cssOrthogonal (cssOrthogonal S) = S := by
  ext x
  constructor
  · intro hx
    by_contra hn
    obtain ⟨z, hz, hdot⟩ := exists_orthogonal_dot_one S x hn
    have hz' := (cssOrthogonal_mem _ _).mp hx z hz
    rw [dotProduct_comm, hdot] at hz'
    exact one_ne_zero hz'
  · intro hx z hz
    rw [dotProduct_comm]
    exact (cssOrthogonal_mem _ _).mp hz x hx

#print axioms cssOrthogonal
#print axioms cssOrthogonal_involutive

end CriticalDepth.Manuscript20261114.CSSCode
