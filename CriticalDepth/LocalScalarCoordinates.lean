import CriticalDepth.ScalarExtension
import CriticalDepth.CircuitParameters

/-!
# Actual local matrix coordinates and scalar-extension support

The polynomial presentation uses coefficients of the standard local matrix
basis. This module binds that formula to the original complex tensor embedding
and to the supported span after any algebraic evaluation into an extension field.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {n : ℕ} {dim : Fin n → ℕ}

theorem matrix_map_self {ι κ : Type*} (A : Matrix ι κ ℂ) :
    A.map (algebraMap ℂ ℂ) = A := by
  ext i j
  simp

theorem matrix_eq_sum_smul_single {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) :
    A = ∑ a, ∑ b, A a b • Matrix.single a b (1 : ℂ) := by
  classical
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    (Matrix.matrix_eq_sum_single A)

private theorem localEmbedLinearMap_apply (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) :
    (localEmbedLinearMap S) A = localEmbed S A := rfl

/-- At complex points the coefficient formula is precisely the original embedding. -/
theorem coefficientEmbed_complex (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) : coefficientEmbed S A = localEmbed S A := by
  classical
  have hmap := congrArg (localEmbedLinearMap (dim := dim) S)
    (matrix_eq_sum_smul_single A)
  have hmap' : localEmbed S A =
      ∑ a, ∑ b, A a b • localEmbed S (Matrix.single a b (1 : ℂ)) := by
    simpa only [map_sum, map_smul, localEmbedLinearMap_apply] using hmap
  calc
    coefficientEmbed S A =
        ∑ a, ∑ b, A a b • localEmbed S (Matrix.single a b (1 : ℂ)) := by
      simp only [coefficientEmbed, matrix_map_self]
    _ = localEmbed S A := hmap'.symm

theorem coefficientEmbed_naturality {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (S : Finset (Fin n))
    (M : Matrix (LocalBasis dim S) (LocalBasis dim S) A) (φ : A →ₐ[ℂ] B) :
    (coefficientEmbed S M).map φ = coefficientEmbed S (M.map φ) := by
  classical
  ext x y
  simp only [coefficientEmbed, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, φ.commutes]

variable {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]

/-- Every arbitrary local extension-field matrix has genuine supported-span membership. -/
theorem coefficientEmbed_mem_supportedSpan (S : Finset (Fin n))
    (A : Matrix (LocalBasis dim S) (LocalBasis dim S) 𝕂) :
    coefficientEmbed S A ∈ supportedSpan (K := 𝕂) S := by
  classical
  unfold coefficientEmbed
  apply (supportedSpan (K := 𝕂) S).sum_mem
  intro a _ha
  apply (supportedSpan (K := 𝕂) S).sum_mem
  intro b _hb
  apply (supportedSpan (K := 𝕂) S).smul_mem
  exact constant_mem_supportedSpan (K := 𝕂) ⟨Matrix.single a b (1 : ℂ), rfl⟩

/-- Polynomial gate evaluation lands in the concrete supported span at every field point. -/
theorem physicalGatePolynomial_map_mem_supportedSpan {ℓ g h : ℕ}
    (support : GateIndex n h → Finset (Fin n)) (p : GateIndex n h) (inverse : Bool)
    (φ : CircuitPolynomial (K := ℓ) (g := g) (dim := dim) support →ₐ[ℂ] 𝕂) :
    (physicalGatePolynomial (K := ℓ) (g := g) (dim := dim) support p inverse).map φ ∈
      supportedSpan (K := 𝕂) (support p) := by
  rw [physicalGatePolynomial, coefficientEmbed_naturality]
  exact coefficientEmbed_mem_supportedSpan _ _

end CriticalDepth.Manuscript
