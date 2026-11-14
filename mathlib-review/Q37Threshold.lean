import BarePauliRotations
import ExactGeneration

/-!
# Arity-three thresholds from the exact distance and bare Z of Q37

The continuous onset follows from the universal finiteness theorem at
depths one and two, and an explicit weight-seven bare Z rotation at
depth three. The exact-word threshold also uses density at depth one.
-/

namespace CriticalDepth.Manuscript20261114.Q37Threshold

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.Arithmetic
open scoped ENat Kronecker

noncomputable section

variable (C : Code 37 (fun _ => 2) 2 1)

private theorem z_nonscalar : ¬ IsScalar SinglePauli.Z.matrix := by
  rintro ⟨z,hz⟩
  have h₀ := congrArg (fun A : Operator (Fin 2) => A 0 0) hz
  have h₁ := congrArg (fun A : Operator (Fin 2) => A 1 1) hz
  have ha : (1 : ℂ) = z := by
    simpa [SinglePauli.matrix, Matrix.one_apply] using h₀
  have hb : (-1 : ℂ) = z := by
    simpa [SinglePauli.matrix, Matrix.one_apply] using h₁
  have hc : (1 : ℂ) = -1 := ha.trans hb.symm
  norm_num at hc

theorem q37ZRotation_mem_depthThree
    (p : Fin 37 → SinglePauli) (hweight : (pauliSupport p).card = 7)
    (hZ : pauliMatrix 0 p * C.encoding =
      C.encoding * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin 1)))) (t : ℝ) :
    projectiveRotation SinglePauli.Z.matrix (singlePauli_selfAdjoint .Z)
      (singlePauli_sq .Z) t ∈ nativeLogicalImage C.encoding 3 3 := by
  have h := barePauli_projectiveRotation_mem_nativeLogicalImage C (by decide) 3 (by decide)
    p SinglePauli.Z.matrix hZ (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) t
  rw [hweight, show max 1 (criticalDepth 3 7) = 3 by decide] at h
  exact h

theorem q37Threshold_continuous
    (hDistance : HasActualDistance C 7)
    (p : Fin 37 → SinglePauli) (hweight : (pauliSupport p).card = 7)
    (hZ : pauliMatrix 0 p * C.encoding =
      C.encoding * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin 1)))) :
    nativeCriticalDepth C.encoding 3 = 3 := by
  apply le_antisymm
  · apply (nativeCriticalDepth_le_nat_iff C.encoding 3 3).mpr
    refine ⟨by decide, ?_⟩
    let S := circleRotationSubgroup SinglePauli.Z.matrix
      (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z)
    have hsub : (S : Set (PU (Fin 2))) ⊆ nativeLogicalImage C.encoding 3 3 :=
      circleRotationSubgroup_subset_of_rotation_mem _ _ _ _
        (q37ZRotation_mem_depthThree C p hweight hZ)
    have hInf : (S : Set (PU (Fin 2))).Infinite := by
      let e := circleRotationEquiv (P := SinglePauli.Z.matrix)
        (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) z_nonscalar
      have hParam : Function.Injective (fun x : ℝ => Circle.exp (Real.arctan x)) := by
        intro x y hxy
        apply Real.arctan_injective
        have hbound : Real.pi / 2 - -(Real.pi / 2) < 2 * Real.pi := by
          linarith [Real.pi_pos]
        exact Circle.exp_injOn_Icc hbound
          (Set.Ioo_subset_Icc_self (Real.arctan_mem_Ioo x))
          (Set.Ioo_subset_Icc_self (Real.arctan_mem_Ioo y)) hxy
      letI : Infinite Circle := Infinite.of_injective _ hParam
      letI : Infinite S := Infinite.of_injective e e.injective
      exact Set.infinite_coe_iff.mp inferInstance
    exact hInf.mono hsub
  · unfold nativeCriticalDepth
    apply le_sInf
    rintro _ ⟨h, hp, rfl, hInf⟩
    apply ENat.natCast_le_natCast.mpr
    by_contra hb
    have hFinite := (nativeTheoremOne_proved 37 2 1 7 (fun _ => 2)
      (by decide) (by decide) (by decide) (by decide) C.encoding C.isometry
      hDistance.1 3 h (by decide) hp
      (by simpa [show criticalDepth 3 7 = 3 by decide] using Nat.lt_of_not_ge hb)).1
    exact hInf hFinite

theorem q37Threshold_exact_lower
    (hDistance : HasActualDistance C 7)
    (p : Fin 37 → SinglePauli) (hweight : (pauliSupport p).card = 7)
    (hZ : pauliMatrix 0 p * C.encoding =
      C.encoding * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin 1)))) :
    (3 : ℕ∞) ≤ nativeExactDepth C.encoding 3 := by
  rw [← q37Threshold_continuous C hDistance p hweight hZ]
  exact (le_max_left _ _).trans (max_nativeCriticalDepth_nativeDenseDepth_le_nativeExactDepth
    C.encoding 3 (by decide))

theorem q37Threshold_one_three_three
    (hDistance : HasActualDistance C 7)
    (p : Fin 37 → SinglePauli) (hweight : (pauliSupport p).card = 7)
    (hZ : pauliMatrix 0 p * C.encoding =
      C.encoding * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin 1))))
    (hDense : (generatedLogicalSubgroup C.encoding 3 1).topologicalClosure = ⊤) :
    nativeDenseDepth C.encoding 3 = 1 ∧
      nativeCriticalDepth C.encoding 3 = 3 ∧ nativeExactDepth C.encoding 3 = 3 := by
  have hdense : nativeDenseDepth C.encoding 3 = 1 := by
    apply le_antisymm
    · exact (nativeDenseDepth_le_nat_iff C.encoding 3 1).mpr ⟨le_rfl,hDense⟩
    · unfold nativeDenseDepth positiveDepthInf
      apply le_sInf
      rintro _ ⟨h,hh,rfl,_⟩
      exact ENat.natCast_le_natCast.mpr hh
  have hcont := q37Threshold_continuous C hDistance p hweight hZ
  refine ⟨hdense,hcont,?_⟩
  rw [nativeExactDepth_eq_max C.encoding C.isometry (by decide) (by decide),
    hcont, hdense]
  decide

#print axioms q37ZRotation_mem_depthThree
#print axioms q37Threshold_continuous
#print axioms q37Threshold_one_three_three

end

end CriticalDepth.Manuscript20261114.Q37Threshold
