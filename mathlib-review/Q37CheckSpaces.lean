import Q37NativeBlocks
import CSSCodeDimension
import CSSCodeDistance

/-!
The actual row spaces of the 37-qubit CSS code and its encoded dimension.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.Manuscript20261114.CSSCheckSpaces

abbrev Q37Word := CSSWord 37

def checkMatrix (rows : List ℕ) : Matrix (Fin rows.length) (Fin 37) CSSBit :=
  fun j => wordOfNatMask 37 rows[j]

def q37XChecks : Submodule CSSBit Q37Word := (checkMatrix xChecks).vecMulLinear.range
def q37ZChecks : Submodule CSSBit Q37Word := (checkMatrix zChecks).vecMulLinear.range

def checkDualMatrix (rows dual : List ℕ) (h : dual.length = rows.length) :
    Matrix (Fin 37) (Fin rows.length) CSSBit :=
  fun j i => wordOfNatMask 37 dual[i.cast h.symm] j

private theorem checkMatrix_finrank (rows : List ℕ)
    (D : Matrix (Fin 37) (Fin rows.length) CSSBit)
    (hD : checkMatrix rows * D = 1) :
    Module.finrank CSSBit (checkMatrix rows).vecMulLinear.range = rows.length := by
  have hi : Function.Injective (checkMatrix rows).vecMulLinear := by
    intro x y h
    have he := congrArg ((· ᵥ* D) : Q37Word → Fin rows.length → CSSBit) h
    change (x ᵥ* checkMatrix rows) ᵥ* D = (y ᵥ* checkMatrix rows) ᵥ* D at he
    rwa [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hD, Matrix.vecMul_one, Matrix.vecMul_one] at he
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
private theorem x_matrix_right_inverse :
    checkMatrix xChecks * checkDualMatrix xChecks xDual (by decide) = 1 := by decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
private theorem z_matrix_right_inverse :
    checkMatrix zChecks * checkDualMatrix zChecks zDual (by decide) = 1 := by decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
private theorem x_z_checks_orthogonal :
    checkMatrix xChecks * (checkMatrix zChecks).transpose = 0 := by decide

theorem q37XChecks_finrank : Module.finrank CSSBit q37XChecks = 18 :=
  (checkMatrix_finrank xChecks _ x_matrix_right_inverse).trans xDual_certificate.1

theorem q37ZChecks_finrank : Module.finrank CSSBit q37ZChecks = 18 :=
  (checkMatrix_finrank zChecks _ z_matrix_right_inverse).trans zDual_certificate.1

theorem checkMatrix_dot (rows checks : List ℕ)
    (u : Fin rows.length → CSSBit) (v : Fin checks.length → CSSBit) :
    dotProduct (u ᵥ* checkMatrix rows) (v ᵥ* checkMatrix checks) =
      dotProduct (u ᵥ* (checkMatrix rows * (checkMatrix checks).transpose)) v := by
  rw [← Matrix.mulVec_transpose (checkMatrix checks) v, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem q37ChecksCompatible : q37XChecks ≤ cssOrthogonal q37ZChecks := by
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  rw [cssOrthogonal_mem]
  rintro _ ⟨v, rfl⟩
  change dotProduct (u ᵥ* checkMatrix xChecks) (v ᵥ* checkMatrix zChecks) = 0
  rw [checkMatrix_dot, x_z_checks_orthogonal, Matrix.vecMul_zero, zero_dotProduct]

theorem q37LogicalQubits : cssLogicalQubits q37XChecks q37ZChecks = 1 := by
  rw [cssLogicalQubits_eq_sub _ _ q37ChecksCompatible, q37XChecks_finrank, q37ZChecks_finrank]

def q37LogicalX : Q37Word := wordOfNatMask 37 logicalX
def q37LogicalZ : Q37Word := wordOfNatMask 37 logicalZ

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
private theorem q37LogicalX_matrix : (checkMatrix zChecks) *ᵥ q37LogicalX = 0 := by decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
private theorem q37LogicalZ_matrix : (checkMatrix xChecks) *ᵥ q37LogicalZ = 0 := by decide

theorem q37LogicalX_in_dual : q37LogicalX ∈ cssOrthogonal q37ZChecks := by
  rw [cssOrthogonal_mem]
  rintro _ ⟨v, rfl⟩
  change dotProduct q37LogicalX (v ᵥ* checkMatrix zChecks) = 0
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, q37LogicalX_matrix, dotProduct_zero]

theorem q37LogicalZ_in_dual : q37LogicalZ ∈ cssOrthogonal q37XChecks := by
  rw [cssOrthogonal_mem]
  rintro _ ⟨v, rfl⟩
  change dotProduct q37LogicalZ (v ᵥ* checkMatrix xChecks) = 0
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, q37LogicalZ_matrix, dotProduct_zero]

theorem q37Logical_dot : dotProduct q37LogicalX q37LogicalZ = 1 := by decide

theorem q37LogicalZ_not_check : q37LogicalZ ∉ q37ZChecks := by
  intro hz
  have ht := (cssOrthogonal_mem _ _).mp q37LogicalX_in_dual q37LogicalZ hz
  rw [q37Logical_dot] at ht
  exact one_ne_zero ht

theorem q37LogicalX_not_check : q37LogicalX ∉ q37XChecks := by
  intro hx
  have ht := (cssOrthogonal_mem _ _).mp q37LogicalZ_in_dual q37LogicalX hx
  rw [dotProduct_comm, q37Logical_dot] at ht
  exact one_ne_zero ht

noncomputable def q37Code :=
  physicalCSSCode q37XChecks q37ZChecks q37ChecksCompatible

#print axioms q37ChecksCompatible
#print axioms q37LogicalQubits
#print axioms q37LogicalZ_not_check
#print axioms q37LogicalX_not_check

end CriticalDepth.Q37BinaryData