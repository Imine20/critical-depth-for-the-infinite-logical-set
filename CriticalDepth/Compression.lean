import CriticalDepth.MatrixCore

/-!
The two-sided frame-transfer step and logical scalarity.

Rectangular encoding matrices use `conjTranspose` explicitly. No isometry
hypothesis is needed for the frame identity itself. The later specialization
uses unitary logical and gauge factors to undo the change of frame.
-/

namespace CriticalDepth

open Matrix
open scoped Kronecker

variable {Phys Code Log Gauge : Type*}
variable [Fintype Phys] [DecidableEq Phys]
variable [Fintype Code] [DecidableEq Code]
variable [Fintype Log] [DecidableEq Log]
variable [Fintype Gauge] [DecidableEq Gauge]

theorem encoded_adjoint
    (U : Operator Phys) (V : Matrix Phys Code ℂ) (T : Operator Code)
    (hencoded : U * V = V * T) :
    V.conjTranspose * U.conjTranspose = T.conjTranspose * V.conjTranspose := by
  have h := congrArg Matrix.conjTranspose hencoded
  simpa only [Matrix.conjTranspose_mul] using h

/-- Compression in the backward frame is conjugation of forward compression. -/
theorem compressed_backward_frame
    (U H : Operator Phys) (V : Matrix Phys Code ℂ) (T : Operator Code)
    (hencoded : U * V = V * T) :
    V.conjTranspose * U.conjTranspose * H * U * V =
      T.conjTranspose * (V.conjTranspose * H * V) * T := by
  calc
    V.conjTranspose * U.conjTranspose * H * U * V =
        (V.conjTranspose * U.conjTranspose) * H * (U * V) := by
          simp only [Matrix.mul_assoc]
    _ = (T.conjTranspose * V.conjTranspose) * H * (V * T) := by
      rw [encoded_adjoint U V T hencoded, hencoded]
    _ = T.conjTranspose * (V.conjTranspose * H * V) * T := by
      simp only [Matrix.mul_assoc]

theorem compressed_forward_of_backward
    (U H : Operator Phys) (V : Matrix Phys Code ℂ) (T B : Operator Code)
    (hencoded : U * V = V * T)
    (hT : T * T.conjTranspose = 1)
    (hbackward : V.conjTranspose * U.conjTranspose * H * U * V = B) :
    V.conjTranspose * H * V = T * B * T.conjTranspose := by
  have hb : T.conjTranspose * (V.conjTranspose * H * V) * T = B := by
    rw [← compressed_backward_frame U H V T hencoded]
    exact hbackward
  calc
    V.conjTranspose * H * V =
        (T * T.conjTranspose) * (V.conjTranspose * H * V) *
          (T * T.conjTranspose) := by rw [hT]; simp
    _ = T * (T.conjTranspose * (V.conjTranspose * H * V) * T) * T.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = T * B * T.conjTranspose := by rw [hb]

theorem conjTranspose_kronecker_operators
    (W : Operator Log) (Z : Operator Gauge) :
    (W ⊗ₖ Z).conjTranspose = W.conjTranspose ⊗ₖ Z.conjTranspose := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.conjTranspose_apply, Matrix.kronecker_apply, map_mul, mul_comm]

theorem kronecker_right_unitary
    (W : Operator Log) (Z : Operator Gauge)
    (hW : W * W.conjTranspose = 1) (hZ : Z * Z.conjTranspose = 1) :
    (W ⊗ₖ Z) * (W ⊗ₖ Z).conjTranspose = 1 := by
  calc
    (W ⊗ₖ Z) * (W ⊗ₖ Z).conjTranspose =
        (W ⊗ₖ Z) * (W.conjTranspose ⊗ₖ Z.conjTranspose) := by
          rw [conjTranspose_kronecker_operators]
    _ = (W * W.conjTranspose) ⊗ₖ (Z * Z.conjTranspose) :=
      (Matrix.mul_kronecker_mul W W.conjTranspose Z Z.conjTranspose).symm
    _ = 1 := by rw [hW, hZ, Matrix.one_kronecker_one]

theorem gauge_kronecker_conjugation
    (W : Operator Log) (Z N : Operator Gauge)
    (hW : W * W.conjTranspose = 1) :
    (W ⊗ₖ Z) * ((1 : Operator Log) ⊗ₖ N) * (W ⊗ₖ Z).conjTranspose =
      (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) := by
  calc
    (W ⊗ₖ Z) * ((1 : Operator Log) ⊗ₖ N) * (W ⊗ₖ Z).conjTranspose =
        ((W * 1) ⊗ₖ (Z * N)) * (W.conjTranspose ⊗ₖ Z.conjTranspose) := by
          rw [← Matrix.mul_kronecker_mul W (1 : Operator Log) Z N,
            conjTranspose_kronecker_operators]
    _ = ((W * 1) * W.conjTranspose) ⊗ₖ ((Z * N) * Z.conjTranspose) :=
      (Matrix.mul_kronecker_mul (W * 1) W.conjTranspose (Z * N) Z.conjTranspose).symm
    _ = (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) := by
      rw [mul_one, hW]

/--
The manuscript's backward-detectable insertion has gauge-only compression in
the forward frame. The physical-unitary hypothesis is retained explicitly;
the matrix identity in fact needs only the encoded equation and unitarity of
the two encoded factors.
-/
theorem gauge_frame_transfer
    (U H : Operator Phys) (V : Matrix Phys (Log × Gauge) ℂ)
    (W : Operator Log) (Z N : Operator Gauge)
    (_hU : IsUnitary U) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hbackward : V.conjTranspose * U.conjTranspose * H * U * V =
      (1 : Operator Log) ⊗ₖ N) :
    V.conjTranspose * H * V =
      (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) := by
  have hWright : W * W.conjTranspose = 1 := hW.2
  have hZright : Z * Z.conjTranspose = 1 := hZ.2
  calc
    V.conjTranspose * H * V =
        (W ⊗ₖ Z) * ((1 : Operator Log) ⊗ₖ N) * (W ⊗ₖ Z).conjTranspose := by
          exact compressed_forward_of_backward U H V (W ⊗ₖ Z) ((1 : Operator Log) ⊗ₖ N)
            hencoded (kronecker_right_unitary W Z hWright hZright) hbackward
    _ = (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) :=
      gauge_kronecker_conjugation W Z N hWright

/--
An individual gauge diagonal block already forces logical scalarity.
Consequently this statement needs no partial-trace normalization or division.
-/
theorem scalarity_of_tensor_generator
    [Nonempty Gauge] (A : Operator Log) (B M : Operator Gauge)
    (h : A ⊗ₖ (1 : Operator Gauge) + (1 : Operator Log) ⊗ₖ B =
      (1 : Operator Log) ⊗ₖ M) : IsScalar A := by
  classical
  let j : Gauge := Classical.choice inferInstance
  refine ⟨M j j - B j j, ?_⟩
  ext i k
  have hh := congrArg (fun X : Operator (Log × Gauge) => X (i, j) (k, j)) h
  by_cases hik : i = k
  · subst k
    simp [Matrix.kronecker_apply] at hh ⊢
    linear_combination hh
  · simpa [Matrix.kronecker_apply, Matrix.one_apply, hik] using hh

end CriticalDepth
