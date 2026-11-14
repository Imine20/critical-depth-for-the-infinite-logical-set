import CriticalDepthMathlib

/-!
# Bare logical Pauli rotations

The same physical Pauli compression circuit implements a logical rotation
with identity action on the gauge register. This only needs the bare
encoding relation, including when the gauge dimension is greater than one.
-/

open scoped Kronecker

namespace CriticalDepth.Manuscript20261114

open Manuscript ReviewV2

noncomputable section

variable {n K g : ℕ} {dim : Fin n → ℕ}

/-- Affine functions preserve an encoding relation with identity on the gauge factor. -/
theorem affine_encoding_bare (C : Code n dim K g)
    (P : Operator (PhysicalBasis n dim)) (A : Operator (Fin K))
    (hencoded : P * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin g))))
    (a b : ℂ) :
    affine P a b * C.encoding =
      C.encoding * (affine A a b ⊗ₖ (1 : Operator (Fin g))) := by
  have htensor : affine A a b ⊗ₖ (1 : Operator (Fin g)) =
      affine (A ⊗ₖ (1 : Operator (Fin g))) a b := by
    simp only [affine, Matrix.add_kronecker, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  calc
    affine P a b * C.encoding = a • C.encoding + b • (P * C.encoding) := by
      simp only [affine, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = C.encoding * affine (A ⊗ₖ (1 : Operator (Fin g))) a b := by
      rw [hencoded]
      simp only [affine, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    _ = C.encoding * (affine A a b ⊗ₖ (1 : Operator (Fin g))) :=
      congrArg (fun M => C.encoding * M) htensor.symm

theorem implements_rotation_bare (C : Code n dim K g)
    (P : Operator (PhysicalBasis n dim)) (A : Operator (Fin K))
    (hencoded : P * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin g))))
    (hself : star A = A) (hsq : A * A = 1) (t : ℝ) :
    Implements C (rotation P t) (rotation A t) := by
  refine ⟨rotation_isUnitary hself hsq t, 1, isUnitary_one, ?_⟩
  exact affine_encoding_bare C P A hencoded (Real.cos t : ℂ)
    (Complex.I * (Real.sin t : ℂ))

/-- Pauli rotations of weight zero or one fit in a single allowed layer. -/
theorem pauli_rotation_synthesis_small (hn : 0 < n) (q : ℕ)
    (p : Fin n → SinglePauli) (hsmall : (pauliSupport p).card ≤ q) (t : ℝ) :
    ∃ c : Circuit n (fun _ => 2) q 1,
      circuitEval c = rotation (pauliMatrix (0 : Fin 4) p) t := by
  classical
  let P := pauliMatrix (0 : Fin 4) p
  have hlocal : SupportedOn (rotation P t) (pauliSupport p) :=
    (pauliMatrix_supportedOn_pauliSupport p).affine (Real.cos t : ℂ)
      (Complex.I * (Real.sin t : ℂ))
  have hunitary : IsUnitary (rotation P t) :=
    rotation_isUnitary (unphased_pauliMatrix_selfAdjoint p) (unphased_pauliMatrix_sq p) t
  let layer := singleGateLayer hn (pauliSupport p) (rotation P t) hsmall hlocal hunitary
  refine ⟨circuitOfLayers [layer], ?_⟩
  rw [circuitOfLayers_eval]
  simpa only [layerSequenceEval, Matrix.one_mul, layer] using
    singleGateLayer_eval hn (pauliSupport p) (rotation P t) hsmall hlocal hunitary

/-- Native depth-bounded logical realization of every angle of a bare Pauli rotation. -/
theorem barePauli_projectiveRotation_mem_nativeLogicalImage
    (C : Code n (fun _ => 2) K g) (hn : 0 < n) (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (A : Operator (Fin K))
    (hencoded : pauliMatrix (0 : Fin 4) p * C.encoding =
      C.encoding * (A ⊗ₖ (1 : Operator (Fin g))))
    (hself : star A = A) (hsq : A * A = 1) (t : ℝ) :
    projectiveRotation A hself hsq t ∈
      nativeLogicalImage C.encoding q (max 1 (Arithmetic.criticalDepth q (pauliSupport p).card)) := by
  classical
  have hsynthesis : ∃ r : ℕ, r ≤ max 1 (Arithmetic.criticalDepth q (pauliSupport p).card) ∧
      ∃ c : Circuit n (fun _ => 2) q r,
        circuitEval c = rotation (pauliMatrix (0 : Fin 4) p) t := by
    by_cases hp : 2 ≤ (pauliSupport p).card
    · exact ⟨_, le_max_right _ _, pauli_rotation_synthesis q hq p hp t⟩
    · exact ⟨1, le_max_left _ _, pauli_rotation_synthesis_small hn q p (by omega) t⟩
  obtain ⟨r, hr, c, hceval⟩ := hsynthesis
  rw [nativeLogicalImage_eq_preimage C.encoding C.isometry]
  change puToProjectiveOperator (Fin K)
      (projectiveMk (Fin K) (unitaryRotation A hself hsq t)) ∈
    arbitraryLogicalImageAtMost C q (max 1 (Arithmetic.criticalDepth q (pauliSupport p).card))
  rw [puToProjectiveOperator_mk]
  apply logicalImage_subset_atMost C q r _ hr
  refine ⟨c, rotation A t, ?_, rfl⟩
  rw [hceval]
  exact implements_rotation_bare C _ A hencoded hself hsq t

theorem barePauli_circle_subset_nativeLogicalImage
    (C : Code n (fun _ => 2) K g) (hn : 0 < n) (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (A : Operator (Fin K))
    (hencoded : pauliMatrix (0 : Fin 4) p * C.encoding =
      C.encoding * (A ⊗ₖ (1 : Operator (Fin g))))
    (hself : star A = A) (hsq : A * A = 1) :
    (circleRotationSubgroup A hself hsq : Set (PU (Fin K))) ⊆
      nativeLogicalImage C.encoding q (max 1 (Arithmetic.criticalDepth q (pauliSupport p).card)) :=
  circleRotationSubgroup_subset_of_rotation_mem A hself hsq _
    (barePauli_projectiveRotation_mem_nativeLogicalImage C hn q hq p A hencoded hself hsq)

#print axioms affine_encoding_bare
#print axioms implements_rotation_bare
#print axioms pauli_rotation_synthesis_small
#print axioms barePauli_projectiveRotation_mem_nativeLogicalImage
#print axioms barePauli_circle_subset_nativeLogicalImage

end

end CriticalDepth.Manuscript20261114
