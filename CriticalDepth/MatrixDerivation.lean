import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

/-!
Entrywise relative derivations and the algebraic gate-insertion product rule.
No differentiability or conjugation on an extension field is assumed here.
This supplies algebraic identities for the proposed alternative proof route;
the circuit-coordinate application remains a separate proof obligation.
-/

namespace CriticalDepth

open Matrix
open scoped BigOperators

variable {F A ι κ μ : Type*} [Field F] [CommRing A] [Algebra F A]

def matrixDerivation (D : Derivation F A A) (M : Matrix ι κ A) : Matrix ι κ A :=
  fun i j => D (M i j)

theorem matrixDerivation_zero (D : Derivation F A A) :
    matrixDerivation D (0 : Matrix ι κ A) = 0 := by
  ext i j
  simp [matrixDerivation]

theorem matrixDerivation_add (D : Derivation F A A) (M N : Matrix ι κ A) :
    matrixDerivation D (M + N) = matrixDerivation D M + matrixDerivation D N := by
  ext i j
  simp [matrixDerivation]

theorem matrixDerivation_constant (D : Derivation F A A) (M : Matrix ι κ F) :
    matrixDerivation D (M.map (algebraMap F A)) = 0 := by
  ext i j
  exact D.map_algebraMap (M i j)

theorem matrixDerivation_one [DecidableEq ι] (D : Derivation F A A) :
    matrixDerivation D (1 : Matrix ι ι A) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [matrixDerivation, Matrix.one_apply, h]

theorem matrixDerivation_mul [Fintype κ] (D : Derivation F A A)
    (M : Matrix ι κ A) (N : Matrix κ μ A) :
    matrixDerivation D (M * N) =
      matrixDerivation D M * N + M * matrixDerivation D N := by
  ext i j
  simp [matrixDerivation, Matrix.mul_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib, mul_comm, add_comm]

theorem matrixDerivation_inverse [Fintype ι] [DecidableEq ι]
    (D : Derivation F A A) (U Uinv : Matrix ι ι A)
    (hU : U * Uinv = 1) (hinv : Uinv * U = 1) :
    matrixDerivation D Uinv = -(Uinv * matrixDerivation D U * Uinv) := by
  have hd : matrixDerivation D U * Uinv + U * matrixDerivation D Uinv = 0 := by
    rw [← matrixDerivation_mul, hU, matrixDerivation_one]
  have hleft := congrArg (fun M : Matrix ι ι A => Uinv * M) hd
  simp only [mul_add, mul_zero, ← mul_assoc, hinv, one_mul] at hleft
  apply eq_neg_iff_add_eq_zero.mpr
  simpa [add_comm] using hleft

/-- Two-factor logarithmic derivative identity, with inverse variables explicit. -/
theorem logarithmic_product_rule [Fintype ι] [DecidableEq ι]
    (D : Derivation F A A) (U V Uinv Vinv : Matrix ι ι A)
    (hV : V * Vinv = 1) :
    matrixDerivation D (U * V) * (Vinv * Uinv) =
      matrixDerivation D U * Uinv +
        U * (matrixDerivation D V * Vinv) * Uinv := by
  rw [matrixDerivation_mul]
  calc
    (matrixDerivation D U * V + U * matrixDerivation D V) * (Vinv * Uinv) =
        matrixDerivation D U * (V * Vinv) * Uinv +
          U * (matrixDerivation D V * Vinv) * Uinv := by noncomm_ring
    _ = _ := by rw [hV]; simp

end CriticalDepth
