import CSSCodeEncoding
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Number of logical qubits in the binary CSS construction
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

private def cssDotForm : LinearMap.BilinForm CSSBit (CSSWord n) :=
  LinearMap.mk₂ CSSBit dotProduct
    (fun x y z => by simp [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun a x z => by simp [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun x y z => by simp [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a x z => by
      simp [dotProduct, Pi.smul_apply, smul_eq_mul, mul_left_comm, Finset.mul_sum])

private theorem cssDotForm_apply (x y : CSSWord n) : cssDotForm x y = dotProduct x y := rfl

private theorem cssDotForm_nondegenerate : (cssDotForm (n := n)).Nondegenerate := by
  have hRefl : (cssDotForm (n := n)).IsRefl := by
    intro x y h
    rw [cssDotForm_apply, dotProduct_comm]
    exact h
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hRefl).mpr ?_
  intro x hx
  funext i
  have h := hx (Pi.single i (1 : CSSBit))
  rw [cssDotForm_apply, dotProduct_single_one] at h
  exact h

private theorem cssOrthogonal_eq_bilin (J : Submodule CSSBit (CSSWord n)) :
    cssOrthogonal J = cssDotForm.orthogonal J := by
  ext x
  rw [cssOrthogonal_mem, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor <;> intro h y hy
  · rw [cssDotForm_apply, dotProduct_comm]
    exact h y hy
  · rw [dotProduct_comm]
    exact h y hy

theorem cssOrthogonal_finrank (J : Submodule CSSBit (CSSWord n)) :
    Module.finrank CSSBit (cssOrthogonal J) = n - Module.finrank CSSBit J := by
  rw [cssOrthogonal_eq_bilin, LinearMap.BilinForm.finrank_orthogonal cssDotForm_nondegenerate,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem cssLogicalQubits_eq_sub (H J : Submodule CSSBit (CSSWord n))
    (hHJ : H ≤ cssOrthogonal J) :
    cssLogicalQubits H J = n - Module.finrank CSSBit H - Module.finrank CSSBit J := by
  let e : insideChecks H J ≃ₗ[CSSBit] H :=
    { toFun x := ⟨x.val.val, x.property⟩
      invFun x := ⟨⟨x.val, hHJ x.property⟩, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hc := Submodule.finrank_quotient_add_finrank (R := CSSBit) (insideChecks H J)
  change cssLogicalQubits H J + Module.finrank CSSBit (insideChecks H J) = _ at hc
  rw [e.finrank_eq, cssOrthogonal_finrank] at hc
  omega

#print axioms cssOrthogonal_finrank
#print axioms cssLogicalQubits_eq_sub

end

end CriticalDepth.Manuscript20261114.CSSCode
