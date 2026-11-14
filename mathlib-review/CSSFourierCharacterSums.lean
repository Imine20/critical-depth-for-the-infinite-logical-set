import CSSCodeCosets
import CSSCodePauliChecks

/-!
# Binary CSS character sums on translated check spaces
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Manuscript20261114.CSSCode

noncomputable section

open Classical

variable {n : ℕ}

local instance (H : Submodule CSSBit (CSSWord n)) : Fintype H := Fintype.ofFinite H

private theorem twice_zero (x : CSSWord n) : x + x = 0 := by
  exact ZModModule.add_self x

/-- A binary character sums to the size of the check space on its dual,
and to zero outside that dual. -/
theorem sum_cssSign_dot (H : Submodule CSSBit (CSSWord n)) (y : CSSWord n) :
    (∑ x : H, cssSign (dotProduct y x.val)) =
      if y ∈ cssOrthogonal H then (Fintype.card H : ℂ) else 0 := by
  classical
  by_cases hy : y ∈ cssOrthogonal H
  · rw [ite_eq_left hy]
    have hzero (x : H) : dotProduct y x.val = 0 := hy x.val x.property
    simp [hzero, cssSign]
  · rw [ite_eq_right hy]
    have hx : ∃ x : H, dotProduct y x.val ≠ 0 := by
      by_contra! hn
      exact hy (fun x hx => hn ⟨x, hx⟩)
    obtain ⟨a, ha⟩ := hx
    let e : H ≃ H :=
      { toFun := fun x => x + a
        invFun := fun x => x + a
        left_inv := by intro x; apply Subtype.ext; change x.val + a.val + a.val = _; rw [add_assoc, twice_zero, add_zero]
        right_inv := by intro x; apply Subtype.ext; change x.val + a.val + a.val = _; rw [add_assoc, twice_zero, add_zero] }
    let f : H → ℂ := fun x => cssSign (dotProduct y x.val)
    have hshift (x : H) : f (e x) = - f x := by
      change cssSign (dotProduct y (x.val + a.val)) = - cssSign (dotProduct y x.val)
      have hs : cssSign (dotProduct y a.val) = -1 := if_neg ha
      rw [dotProduct_add, cssSign_add, hs, mul_neg, mul_one]
    have hsum : (∑ x : H, f x) = -(∑ x : H, f x) := by
      calc
        _ = ∑ x : H, f (e x) := (e.sum_comp f).symm
        _ = ∑ x : H, -f x := Finset.sum_congr rfl (fun x _ => hshift x)
        _ = _ := Finset.sum_neg_distrib f
    change (∑ x : H, f x) = 0
    linear_combination (1 / 2 : ℂ) * hsum

/-- A specific representative identifies its coset support with the
translation of the X-check space by that representative. -/
theorem cosetWords_eq_translate (H J : Submodule CSSBit (CSSWord n))
    (hHJ : H ≤ cssOrthogonal J) (r : cssOrthogonal J) :
    cosetWords H J ((insideChecks H J).mkQ r) =
      Finset.univ.map ⟨fun x : H => r.val + x.val,
        fun _ _ h => Subtype.ext (add_left_cancel h)⟩ := by
  classical
  ext x
  rw [mem_cosetWords]
  constructor
  · rintro ⟨hx, hq⟩
    let u : cssOrthogonal J := ⟨x, hx⟩
    have hd : (insideChecks H J).mkQ (u - r) = 0 := by
      rw [map_sub, show (insideChecks H J).mkQ u = (insideChecks H J).mkQ r from hq, sub_self]
    have hmem : u - r ∈ insideChecks H J := (Submodule.Quotient.mk_eq_zero _).mp hd
    refine Finset.mem_map.mpr ⟨⟨x - r.val, hmem⟩, Finset.mem_univ _, ?_⟩
    change r.val + (x - r.val) = x
    abel
  · intro hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hv
    let b : cssOrthogonal J := ⟨a.val, hHJ a.property⟩
    refine ⟨(r + b).property, ?_⟩
    have hb : (insideChecks H J).mkQ b = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr a.property
    change (insideChecks H J).mkQ (r + b) = _
    rw [map_add, hb, add_zero]

/-- The Fourier character of one CSS coset is supported on the dual
check space, with sign determined by its representative. -/
theorem sum_cssSign_dot_coset (H J : Submodule CSSBit (CSSWord n))
    (hHJ : H ≤ cssOrthogonal J) (r : cssOrthogonal J) (y : CSSWord n) :
    (∑ x ∈ cosetWords H J ((insideChecks H J).mkQ r), cssSign (dotProduct y x)) =
      if y ∈ cssOrthogonal H then
        (Fintype.card H : ℂ) * cssSign (dotProduct y r.val) else 0 := by
  classical
  rw [cosetWords_eq_translate H J hHJ r, Finset.sum_map]
  change (∑ a : H, cssSign (dotProduct y (r.val + a.val))) = _
  simp_rw [dotProduct_add, cssSign_add]
  rw [← Finset.mul_sum, sum_cssSign_dot H]
  split <;> simp [mul_comm]

#print axioms sum_cssSign_dot
#print axioms cosetWords_eq_translate
#print axioms sum_cssSign_dot_coset

end

end CriticalDepth.Manuscript20261114.CSSCode
