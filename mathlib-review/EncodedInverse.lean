import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Recovering the inverse variables in the circuit coordinate algebra

The two encoding equations in the supplemental proof imply that compression
of the inverse circuit inverts the encoded tensor. The two factor inverses
can then be read from its products with the opposite tensor factors.
-/

open scoped BigOperators Kronecker

namespace CriticalDepth.Manuscript20261114

theorem encodedKronecker_inverse {R P L G : Type*} [CommRing R]
    [Fintype P] [DecidableEq P] [Fintype L] [DecidableEq L]
    [Fintype G] [DecidableEq G]
    (E : Matrix (L × G) P R) (V : Matrix P (L × G) R)
    (U Ui : Matrix P P R) (W : Matrix L L R) (Z : Matrix G G R)
    (hEV : E * V = 1) (hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hdual : E * U = (W ⊗ₖ Z) * E) :
    (E * Ui * V) * (W ⊗ₖ Z) = 1 ∧
      (W ⊗ₖ Z) * (E * Ui * V) = 1 := by
  constructor
  · calc
      (E * Ui * V) * (W ⊗ₖ Z) = E * (Ui * (V * (W ⊗ₖ Z))) := by
        simp only [Matrix.mul_assoc]
      _ = E * (Ui * (U * V)) := by rw [← hencoded]
      _ = 1 := by rw [← Matrix.mul_assoc Ui U V, hUiU, Matrix.one_mul, hEV]
  · calc
      (W ⊗ₖ Z) * (E * Ui * V) = ((W ⊗ₖ Z) * E) * Ui * V := by
        simp only [Matrix.mul_assoc]
      _ = (E * U) * Ui * V := by rw [← hdual]
      _ = 1 := by rw [Matrix.mul_assoc E U Ui, hUUi, Matrix.mul_one, hEV]

/-- Extract the two inverse matrices from the specified diagonal blocks. -/
theorem kroneckerFactor_inverses {R L G : Type*} [CommRing R]
    [Fintype L] [DecidableEq L] [Fintype G] [DecidableEq G]
    (logicalIndex : L) (gaugeIndex : G)
    (W : Matrix L L R) (Z : Matrix G G R) (B : Matrix (L × G) (L × G) R)
    (hB : (W ⊗ₖ Z) * B = 1) :
    let WB := ((1 : Matrix L L R) ⊗ₖ Z) * B
    let ZB := (W ⊗ₖ (1 : Matrix G G R)) * B
    let Wi : Matrix L L R := fun i k => WB (i, gaugeIndex) (k, gaugeIndex)
    let Zi : Matrix G G R := fun j l => ZB (logicalIndex, j) (logicalIndex, l)
    W * Wi = 1 ∧ Wi * W = 1 ∧ Z * Zi = 1 ∧ Zi * Z = 1 := by
  intro WB ZB Wi Zi
  have hW : (W ⊗ₖ (1 : Matrix G G R)) * WB = 1 := by
    change (W ⊗ₖ (1 : Matrix G G R)) * (((1 : Matrix L L R) ⊗ₖ Z) * B) = 1
    rw [← mul_assoc, ← Matrix.mul_kronecker_mul, mul_one, one_mul, hB]
  have hZ : ((1 : Matrix L L R) ⊗ₖ Z) * ZB = 1 := by
    change ((1 : Matrix L L R) ⊗ₖ Z) * ((W ⊗ₖ (1 : Matrix G G R)) * B) = 1
    rw [← mul_assoc, ← Matrix.mul_kronecker_mul, one_mul, mul_one, hB]
  have hWi : W * Wi = 1 := by
    ext i k
    rw [Matrix.mul_apply]
    have entry := congrArg
      (fun M : Matrix (L × G) (L × G) R => M (i, gaugeIndex) (k, gaugeIndex)) hW
    simpa only [Wi, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
      Matrix.one_apply, Prod.mk.injEq, and_true, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Fintype.sum_ite_eq, eq_self_iff_true] using entry
  have hZi : Z * Zi = 1 := by
    ext j l
    rw [Matrix.mul_apply]
    have entry := congrArg
      (fun M : Matrix (L × G) (L × G) R => M (logicalIndex, j) (logicalIndex, l)) hZ
    simpa only [Zi, Matrix.mul_apply, Fintype.sum_prod_type_right, Matrix.kronecker_apply,
      Matrix.one_apply, Prod.mk.injEq, true_and, mul_ite, one_mul, mul_zero,
      ite_mul, zero_mul, Fintype.sum_ite_eq, eq_self_iff_true] using entry
  exact ⟨hWi, mul_eq_one_symm hWi, hZi, mul_eq_one_symm hZi⟩

#print axioms encodedKronecker_inverse
#print axioms kroneckerFactor_inverses

end CriticalDepth.Manuscript20261114
