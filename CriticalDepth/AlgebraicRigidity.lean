import CriticalDepth.MatrixDerivation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Algebraic infinitesimal rigidity of an encoded factorization

All matrices in this module have entries in the extension field `K`.
Inverse matrices and the encoding dual are explicit algebraic variables;
there is no conjugation operation on `K` and no implicit Hermitian premise.
The circuit-support and distance argument producing gauge-only compression
is a separate obligation.
-/

namespace CriticalDepth

open Matrix
open scoped Kronecker

variable {F K Phys Log Gauge : Type*}
variable [Field F] [Field K] [Algebra F K]
variable [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log]
variable [Fintype Gauge] [DecidableEq Gauge]

theorem matrixDerivation_kronecker (D : Derivation F K K)
    (A : Matrix Log Log K) (B : Matrix Gauge Gauge K) :
    matrixDerivation D (A ⊗ₖ B) =
      matrixDerivation D A ⊗ₖ B + A ⊗ₖ matrixDerivation D B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [matrixDerivation, Matrix.kronecker_apply, Derivation.leibniz,
    smul_eq_mul, mul_comm, add_comm]

/-- One gauge diagonal block forces the logical generator to be scalar. -/
theorem scalarity_of_tensor_generator_overField [Nonempty Gauge]
    (A : Matrix Log Log K) (B M : Matrix Gauge Gauge K)
    (h : A ⊗ₖ (1 : Matrix Gauge Gauge K) + (1 : Matrix Log Log K) ⊗ₖ B =
      (1 : Matrix Log Log K) ⊗ₖ M) :
    ∃ scalar : K, A = scalar • (1 : Matrix Log Log K) := by
  classical
  let j : Gauge := Classical.choice inferInstance
  refine ⟨M j j - B j j, ?_⟩
  ext i k
  have hh := congrArg (fun X : Matrix (Log × Gauge) (Log × Gauge) K => X (i, j) (k, j)) h
  by_cases hik : i = k
  · subst k
    simp [Matrix.kronecker_apply] at hh ⊢
    linear_combination hh
  · simpa [Matrix.kronecker_apply, Matrix.one_apply, hik] using hh

/-- The encoded logarithmic derivative splits into logical and gauge terms. -/
theorem encoded_logarithmic_generator
    (D : Derivation F K K)
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi : Matrix Gauge Gauge K)
    (hEV : E * V = 1)
    (_hE : matrixDerivation D E = 0) (hV : matrixDerivation D V = 0)
    (_hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (_hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (_hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (_hdual : E * U = (W ⊗ₖ Z) * E) :
    E * (matrixDerivation D U * Ui) * V =
      (matrixDerivation D W * Wi) ⊗ₖ (1 : Matrix Gauge Gauge K) +
        (1 : Matrix Log Log K) ⊗ₖ (matrixDerivation D Z * Zi) := by
  have hTTi : (W ⊗ₖ Z) * (Wi ⊗ₖ Zi) = 1 := by
    rw [← Matrix.mul_kronecker_mul W Wi Z Zi, hWWi, hZZi,
      Matrix.one_kronecker_one]
  have hUiV : Ui * V = V * (Wi ⊗ₖ Zi) := by
    calc
      Ui * V = (Ui * V) * ((W ⊗ₖ Z) * (Wi ⊗ₖ Zi)) := by rw [hTTi]; simp
      _ = Ui * (V * (W ⊗ₖ Z)) * (Wi ⊗ₖ Zi) := by simp only [Matrix.mul_assoc]
      _ = Ui * (U * V) * (Wi ⊗ₖ Zi) := by rw [← hencoded]
      _ = V * (Wi ⊗ₖ Zi) := by simp only [← Matrix.mul_assoc, hUiU, Matrix.one_mul]
  have hdUV : matrixDerivation D U * V = V * matrixDerivation D (W ⊗ₖ Z) := by
    have hh := congrArg (matrixDerivation D) hencoded
    simpa only [matrixDerivation_mul, hV, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add] using hh
  calc
    E * (matrixDerivation D U * Ui) * V = E * (matrixDerivation D U * (Ui * V)) := by
      simp only [Matrix.mul_assoc]
    _ = E * (matrixDerivation D U * (V * (Wi ⊗ₖ Zi))) := by rw [hUiV]
    _ = E * (matrixDerivation D U * V) * (Wi ⊗ₖ Zi) := by
      simp only [Matrix.mul_assoc]
    _ = E * (V * matrixDerivation D (W ⊗ₖ Z)) * (Wi ⊗ₖ Zi) := by rw [hdUV]
    _ = matrixDerivation D (W ⊗ₖ Z) * (Wi ⊗ₖ Zi) := by
      simp only [← Matrix.mul_assoc, hEV, one_mul]
    _ = (matrixDerivation D W * Wi) ⊗ₖ (1 : Matrix Gauge Gauge K) +
        (1 : Matrix Log Log K) ⊗ₖ (matrixDerivation D Z * Zi) := by
      rw [matrixDerivation_kronecker, add_mul,
        ← Matrix.mul_kronecker_mul (matrixDerivation D W) Wi Z Zi,
        ← Matrix.mul_kronecker_mul W Wi (matrixDerivation D Z) Zi,
        hWWi, hZZi]

theorem matrixDerivation_of_scalar_logarithmic_derivative
    (D : Derivation F K K) (W Wi : Matrix Log Log K) (scalar : K)
    (hWiW : Wi * W = 1)
    (hscalar : matrixDerivation D W * Wi = scalar • (1 : Matrix Log Log K)) :
    matrixDerivation D W = scalar • W := by
  calc
    matrixDerivation D W = (matrixDerivation D W * Wi) * W := by
      simp only [Matrix.mul_assoc, hWiW, mul_one]
    _ = (scalar • (1 : Matrix Log Log K)) * W := by rw [hscalar]
    _ = scalar • W := by simp [smul_mul_assoc]

theorem matrixDerivation_inverse_of_scalar_derivative
    (D : Derivation F K K) (W Wi : Matrix Log Log K) (scalar : K)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hscalar : matrixDerivation D W = scalar • W) :
    matrixDerivation D Wi = -(scalar • Wi) := by
  rw [matrixDerivation_inverse D W Wi hWWi hWiW, hscalar]
  simp only [mul_smul_comm, smul_mul_assoc, ← Matrix.mul_assoc, hWiW, one_mul]

theorem projective_coordinates_derivation_zero_of_scalar_derivatives
    (D : Derivation F K K) (W Wi : Matrix Log Log K) (scalar : K)
    (hW : matrixDerivation D W = scalar • W)
    (hWi : matrixDerivation D Wi = -(scalar • Wi)) :
    ∀ a b c d : Log, D (W a b * Wi c d) = 0 := by
  intro a b c d
  have hw := congrArg (fun A : Matrix Log Log K => A a b) hW
  have hwi := congrArg (fun A : Matrix Log Log K => A c d) hWi
  change D (W a b) = scalar * W a b at hw
  change D (Wi c d) = -(scalar * Wi c d) at hwi
  rw [D.leibniz, hw, hwi]
  simp only [smul_eq_mul]
  ring

/--
Gauge-only compression kills every coordinate of the logical conjugation
action. The compression premise must still be established from the concrete
circuit and code-distance hypotheses.
-/
theorem encoded_logarithmic_rigidity [Nonempty Gauge]
    (D : Derivation F K K)
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi M : Matrix Gauge Gauge K)
    (hEV : E * V = 1)
    (hE : matrixDerivation D E = 0) (hV : matrixDerivation D V = 0)
    (hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hdual : E * U = (W ⊗ₖ Z) * E)
    (hcompression : E * (matrixDerivation D U * Ui) * V =
      (1 : Matrix Log Log K) ⊗ₖ M) :
    ∃ scalar : K,
      matrixDerivation D W * Wi = scalar • (1 : Matrix Log Log K) ∧
      matrixDerivation D W = scalar • W ∧
      matrixDerivation D Wi = -(scalar • Wi) ∧
      ∀ a b c d : Log, D (W a b * Wi c d) = 0 := by
  have hgenerator := encoded_logarithmic_generator D E V U Ui W Wi Z Zi
    hEV hE hV hUUi hUiU hWWi hWiW hZZi hZiZ hencoded hdual
  have htensor : (matrixDerivation D W * Wi) ⊗ₖ (1 : Matrix Gauge Gauge K) +
      (1 : Matrix Log Log K) ⊗ₖ (matrixDerivation D Z * Zi) =
        (1 : Matrix Log Log K) ⊗ₖ M := hgenerator.symm.trans hcompression
  obtain ⟨scalar, hscalar⟩ := scalarity_of_tensor_generator_overField
    (matrixDerivation D W * Wi) (matrixDerivation D Z * Zi) M htensor
  have hdW := matrixDerivation_of_scalar_logarithmic_derivative D W Wi scalar hWiW hscalar
  have hdWi := matrixDerivation_inverse_of_scalar_derivative D W Wi scalar hWWi hWiW hdW
  exact ⟨scalar, hscalar, hdW, hdWi,
    projective_coordinates_derivation_zero_of_scalar_derivatives D W Wi scalar hdW hdWi⟩

theorem encoded_projective_coordinates_derivation_zero [Nonempty Gauge]
    (D : Derivation F K K)
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi M : Matrix Gauge Gauge K)
    (hEV : E * V = 1)
    (hE : matrixDerivation D E = 0) (hV : matrixDerivation D V = 0)
    (hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hdual : E * U = (W ⊗ₖ Z) * E)
    (hcompression : E * (matrixDerivation D U * Ui) * V =
      (1 : Matrix Log Log K) ⊗ₖ M) :
    ∀ a b c d : Log, D (W a b * Wi c d) = 0 := by
  obtain ⟨scalar, hscalar, hdW, hdWi, hcoords⟩ :=
    encoded_logarithmic_rigidity D E V U Ui W Wi Z Zi M
      hEV hE hV hUUi hUiU hWWi hWiW hZZi hZiZ hencoded hdual hcompression
  exact hcoords

end CriticalDepth
