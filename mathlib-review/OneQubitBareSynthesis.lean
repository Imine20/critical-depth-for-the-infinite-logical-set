import OneQubitEuler
import BarePauliRotations
import GenerationThresholds

/-!
# Exact one-qubit synthesis from native bare Pauli rotations

The logical synthesis uses three projective rotations. Each of the two
physical Pauli representatives may have its own support weight.
-/

open scoped ENat Kronecker

namespace CriticalDepth.Manuscript20261114.OneQubitEuler

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.Arithmetic

variable {n g : ℕ}

/-- The two bare Pauli representatives give an upper bound at their
larger native rotation depth. -/
theorem nativeExactDepth_le_of_bare_XZ
    (C : Code n (fun _ => 2) 2 g) (hn : 0 < n) (q : ℕ) (hq : 2 ≤ q)
    (pX pZ : Fin n → SinglePauli)
    (hX : pauliMatrix 0 pX * C.encoding =
      C.encoding * (SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin g))))
    (hZ : pauliMatrix 0 pZ * C.encoding =
      C.encoding * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin g)))) :
    nativeExactDepth C.encoding q ≤
      (max (max 1 (criticalDepth q (pauliSupport pX).card))
        (max 1 (criticalDepth q (pauliSupport pZ).card)) : ℕ) := by
  let dx := max 1 (criticalDepth q (pauliSupport pX).card)
  let dz := max 1 (criticalDepth q (pauliSupport pZ).card)
  let d := max dx dz
  apply (nativeExactDepth_le_nat_iff C.encoding q d).mpr
  refine ⟨(le_max_left 1 _).trans (le_max_left dx dz), ?_⟩
  apply subgroup_eq_top_of_has_XZ
  · intro t
    apply Subgroup.subset_closure
    apply nativeLogicalImage_mono_depth C.encoding q (le_max_left dx dz)
    exact barePauli_projectiveRotation_mem_nativeLogicalImage C hn q hq pX
      SinglePauli.X.matrix hX (singlePauli_selfAdjoint .X) (singlePauli_sq .X) t
  · intro t
    apply Subgroup.subset_closure
    apply nativeLogicalImage_mono_depth C.encoding q (le_max_right dx dz)
    exact barePauli_projectiveRotation_mem_nativeLogicalImage C hn q hq pZ
      SinglePauli.Z.matrix hZ (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) t

/-- Matched rotation budgets yield exact native synthesis. This version
also applies when one axis is obtained by conjugation in the generated group. -/
theorem nativeExactDepth_le_of_generated_XZ
    (C : Code n (fun _ => 2) 2 g) (q h : ℕ) (hh : 1 ≤ h)
    (hX : ∀ t, projectiveX t ∈ generatedLogicalSubgroup C.encoding q h)
    (hZ : ∀ t, projectiveZ t ∈ generatedLogicalSubgroup C.encoding q h) :
    nativeExactDepth C.encoding q ≤ h :=
  (nativeExactDepth_le_nat_iff C.encoding q h).mpr
    ⟨hh, subgroup_eq_top_of_has_XZ _ hX hZ⟩

theorem criticalDepth_mono_weight (q : ℕ) {a b : ℕ} (hab : a ≤ b) :
    criticalDepth q a ≤ criticalDepth q b := by
  have h := Nat.clog_mono_right q hab
  unfold criticalDepth
  omega

theorem criticalDepth_positive_of_two_ge (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    1 ≤ criticalDepth q d := by
  have h := clog_pos_of_two_le q d hq hd
  unfold criticalDepth
  omega

/-- If both physical bare axes have weights within the same logarithmic
shell, the larger weight does not increase the exact synthesis depth. -/
theorem nativeExactDepth_le_criticalDepth_of_shell
    (C : Code n (fun _ => 2) 2 g) (hn : 0 < n) (q a : ℕ) (hq : 2 ≤ q) (ha : 2 ≤ a)
    (pX pZ : Fin n → SinglePauli)
    (hX : pauliMatrix 0 pX * C.encoding =
      C.encoding * (SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin g))))
    (hZ : pauliMatrix 0 pZ * C.encoding =
      C.encoding * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin g))))
    (hWX : (pauliSupport pX).card ≤ q ^ Nat.clog q a)
    (hWZ : (pauliSupport pZ).card ≤ q ^ Nat.clog q a) :
    nativeExactDepth C.encoding q ≤ (criticalDepth q a : ℕ∞) := by
  refine (nativeExactDepth_le_of_bare_XZ C hn q hq pX pZ hX hZ).trans ?_
  apply ENat.natCast_le_natCast.mpr
  have hqx := (Nat.clog_le_iff_le_pow (by omega : 1 < q)).mpr hWX
  have hqz := (Nat.clog_le_iff_le_pow (by omega : 1 < q)).mpr hWZ
  have hpos := criticalDepth_positive_of_two_ge q a hq ha
  unfold criticalDepth at *
  omega

#print axioms nativeExactDepth_le_of_bare_XZ
#print axioms nativeExactDepth_le_of_generated_XZ
#print axioms nativeExactDepth_le_criticalDepth_of_shell

end CriticalDepth.Manuscript20261114.OneQubitEuler
