import CriticalDepth.PauliSynthesis

/-!
# The stabilizer upper construction and the explicit reduction of Theorem 2

The continuous subgroup and infinite image are constructed from the original
stabilizer and actual-distance assumptions. The final equality is explicitly
conditional on `theoremOne`; this module does not present that premise as a
closed proof of the first manuscript theorem.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

variable {n ℓ g d k q : ℕ} {dim : Fin n → ℕ}

/-- The canonical subspace logical matrix has an exact identity gauge factor. -/
theorem stabilizer_exact_logicalPauli
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    ∃ (p : Fin n → SinglePauli) (W : Operator (Fin (2 ^ k))),
      (pauliSupport p).card = d ∧
      pauliMatrix (0 : Fin 4) p * C.encoding =
        C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))) ∧
      star W = W ∧ W * W = 1 ∧ ¬ IsScalar W := by
  classical
  obtain ⟨p, hcard, hnongauge⟩ := actualDistance_exists_nongauge_unphasedPauli C hdistance
  obtain ⟨S, hpauli, hspace⟩ := hstabilizer
  let P := pauliMatrix (0 : Fin 4) p
  have hcomm := pauli_commutes_stabilizer_of_nongauge C S hpauli hspace p hnongauge
  have hpreserve := code_preservation_of_stabilizer_commutation C S hspace P hcomm
  let W := subspaceLogicalMatrix C P
  have hself : star W = W :=
    subspaceLogicalMatrix_selfAdjoint C P (unphased_pauliMatrix_selfAdjoint p)
  have hsq : W * W = 1 :=
    subspaceLogicalMatrix_sq_of_preserving C P (unphased_pauliMatrix_sq p) hpreserve
  refine ⟨p, W, hcard, ?_, hself, hsq,
    subspaceLogicalMatrix_nonscalar_of_nongauge C P hnongauge⟩
  exact hpreserve.trans (congrArg (fun A => C.encoding * A)
    (subspaceCompression_eq_kronecker C P))

theorem affine_encoding_subspace (C : Code n dim ℓ 1)
    (P : Operator (PhysicalBasis n dim)) (W : Operator (Fin ℓ))
    (hencoded : P * C.encoding = C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))))
    (a b : ℂ) :
    affine P a b * C.encoding =
      C.encoding * (affine W a b ⊗ₖ (1 : Operator (Fin 1))) := by
  have htensor : affine W a b ⊗ₖ (1 : Operator (Fin 1)) =
      affine (W ⊗ₖ (1 : Operator (Fin 1))) a b := by
    simp only [affine, Matrix.add_kronecker, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  calc
    affine P a b * C.encoding = a • C.encoding + b • (P * C.encoding) := by
      simp only [affine, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = C.encoding * affine (W ⊗ₖ (1 : Operator (Fin 1))) a b := by
      rw [hencoded]
      simp only [affine, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    _ = C.encoding * (affine W a b ⊗ₖ (1 : Operator (Fin 1))) :=
      congrArg (fun A => C.encoding * A) htensor.symm

theorem implements_rotation_subspace (C : Code n dim ℓ 1)
    (P : Operator (PhysicalBasis n dim)) (W : Operator (Fin ℓ))
    (hencoded : P * C.encoding = C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))))
    (hself : star W = W) (hsq : W * W = 1) (t : ℝ) :
    Implements C (rotation P t) (rotation W t) := by
  refine ⟨rotation_isUnitary hself hsq t, 1, isUnitary_one, ?_⟩
  exact affine_encoding_subspace C P W hencoded (Real.cos t : ℂ)
    (Complex.I * (Real.sin t : ℂ))

theorem implements_rationalRotation_subspace (C : Code n dim ℓ 1)
    (P : Operator (PhysicalBasis n dim)) (W : Operator (Fin ℓ))
    (hencoded : P * C.encoding = C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))))
    (hself : star W = W) (hsq : W * W = 1) (r : ℕ) :
    Implements C (rationalRotation P r) (rationalRotation W r) := by
  refine ⟨rationalRotation_isUnitary hself hsq r, 1, isUnitary_one, ?_⟩
  exact affine_encoding_subspace C P W hencoded (rationalScale r)
    (rationalScale r * Complex.I * (r : ℂ))

/-- Both upper-endpoint conclusions follow from the original stabilizer hypotheses. -/
theorem stabilizer_critical_logical_image (C : Code n (fun _ => 2) (2 ^ k) 1)
    (_hk : 1 ≤ k) (hd : 2 ≤ d) (hq : 2 ≤ q)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    (logicalImage C q (Arithmetic.criticalDepth q d)).Infinite ∧
      HasContinuousLogicalSubgroup C q (Arithmetic.criticalDepth q d) := by
  classical
  obtain ⟨p, W, hcard, hencoded, hself, hsq, hnonscalar⟩ :=
    stabilizer_exact_logicalPauli C hstabilizer hdistance
  have hpdist : 2 ≤ (pauliSupport p).card := by omega
  have hrational : ∀ r : ℕ,
      projectiveClass (rationalRotation W r) ∈
        logicalImage C q (Arithmetic.criticalDepth q d) := by
    intro r
    have hsynth := pauli_rationalRotation_synthesis q hq p hpdist r
    rw [hcard] at hsynth
    obtain ⟨c, hceval⟩ := hsynth
    refine ⟨c, rationalRotation W r, ?_, rfl⟩
    rw [hceval]
    exact implements_rationalRotation_subspace C _ W hencoded hself hsq r
  have hrotation : ∀ t : ℝ,
      projectiveClass (rotation W t) ∈ logicalImage C q (Arithmetic.criticalDepth q d) := by
    intro t
    have hsynth := pauli_rotation_synthesis q hq p hpdist t
    rw [hcard] at hsynth
    obtain ⟨c, hceval⟩ := hsynth
    refine ⟨c, rotation W t, ?_, rfl⟩
    rw [hceval]
    exact implements_rotation_subspace C _ W hencoded hself hsq t
  constructor
  · apply (rationalRotation_classes_infinite hnonscalar).mono
    rintro a ⟨r, rfl⟩
    exact hrational r
  · refine ⟨rotation W, continuous_rotation W, rotation_isUnitary hself hsq,
      rotation_zero W, rotation_add hsq, ?_, hrotation⟩
    exact ⟨Real.pi / 2, rotation_pi_div_two_not_projectivelyEquivalent_one hnonscalar⟩

theorem hInfinity_eq_of_finite_below_and_infinite_at
    (C : Code n dim ℓ g) (q H : ℕ)
    (hbelow : ∀ h : ℕ, h < H → (logicalImage C q h).Finite)
    (hat : (logicalImage C q H).Infinite) : hInfinity C q = (H : ℕ∞) := by
  unfold hInfinity
  apply le_antisymm
  · exact sInf_le ⟨H, rfl, hat⟩
  · apply le_sInf
    rintro r ⟨h, rfl, hinfinite⟩
    have hnat : H ≤ h := by
      by_contra hn
      have hlt : h < H := by omega
      exact hinfinite (hbelow h hlt)
    exact_mod_cast hnat

private theorem two_le_two_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      rw [pow_succ]
      omega

private theorem sites_positive_of_actualDistance
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hd : 2 ≤ d)
    (hdistance : HasActualDistance C d) : 1 ≤ n := by
  obtain ⟨p, hcard, _hnongauge⟩ := actualDistance_exists_nongauge_unphasedPauli C hdistance
  have hsites : (pauliSupport p).card ≤ n := by
    calc
      (pauliSupport p).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- Explicit conditional reduction: the sole remaining theorem premise is Theorem 1. -/
theorem theoremTwo_of_theoremOne (hT1 : theoremOne) : theoremTwo := by
  intro n k d q hk hd hq C hstabilizer hdistance
  obtain ⟨hinfinite, hcontinuous⟩ :=
    stabilizer_critical_logical_image C hk hd hq hstabilizer hdistance
  refine ⟨?_, hcontinuous⟩
  apply hInfinity_eq_of_finite_below_and_infinite_at C q (Arithmetic.criticalDepth q d) ?_ hinfinite
  intro h hh
  exact hT1 n (2 ^ k) 1 d (fun _ => 2)
    (sites_positive_of_actualDistance C hd hdistance) (two_le_two_pow k hk) (by decide) hd
    C hdistance.1 q h (Or.inl ⟨hq, hh⟩)

end CriticalDepth.Manuscript
