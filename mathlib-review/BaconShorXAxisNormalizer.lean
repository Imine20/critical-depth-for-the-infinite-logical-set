import BaconShorThresholdUpper
import BaconShorGaugeTrace

/-!
# Projective axis normalizer and aspect-ratio depth bound

The proof here consumes the local normalized-gauge-trace bound.
The bound itself is an independent Pauli expansion calculation.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.Arithmetic
open CriticalDepth.Manuscript20261114
open Matrix
open scoped BigOperators ENat Kronecker

noncomputable section

def preservesXAxis (U : Matrix.unitaryGroup (Fin 2) ℂ) : Prop :=
  U.val * SinglePauli.X.matrix * star U.val = SinglePauli.X.matrix ∨
    U.val * SinglePauli.X.matrix * star U.val = -SinglePauli.X.matrix

private theorem X_axis_normalizer_mul (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (hU : preservesXAxis U) (hV : preservesXAxis V) : preservesXAxis (U*V) := by
  have he : (U * V).val * SinglePauli.X.matrix * star (U * V).val =
      U.val * (V.val * SinglePauli.X.matrix * star V.val) * star U.val := by
    change (U.val * V.val) * SinglePauli.X.matrix * star (U.val * V.val) = _
    simp [star_mul, mul_assoc]
  unfold preservesXAxis
  rw [he]
  rcases hU with hU | hU <;> rcases hV with hV | hV <;>
    simp [hV, Matrix.mul_neg, Matrix.neg_mul, hU]

private theorem X_axis_normalizer_inv (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (hU : preservesXAxis U) : preservesXAxis U⁻¹ := by
  have h₁ : star U.val * U.val = 1 :=
    ((isUnitary_iff_mem_unitaryGroup (Fin 2) U.val).mpr U.property).1
  unfold preservesXAxis
  rw [Matrix.UnitaryGroup.inv_val, star_star]
  change star U.val * SinglePauli.X.matrix * U.val = SinglePauli.X.matrix ∨
    star U.val * SinglePauli.X.matrix * U.val = -SinglePauli.X.matrix
  rcases hU with h | h
  · left
    have hh := congrArg (fun A : Operator (Fin 2) => star U.val * A * U.val) h
    change star U.val * (U.val * SinglePauli.X.matrix * star U.val) * U.val =
      star U.val * SinglePauli.X.matrix * U.val at hh
    rw [← Matrix.mul_assoc (star U.val), ← Matrix.mul_assoc,
      h₁, Matrix.one_mul, Matrix.mul_assoc, h₁, Matrix.mul_one] at hh
    exact hh.symm
  · right
    have hh := congrArg (fun A : Operator (Fin 2) => star U.val * A * U.val) h
    change star U.val * (U.val * SinglePauli.X.matrix * star U.val) * U.val =
      star U.val * (-SinglePauli.X.matrix) * U.val at hh
    rw [← Matrix.mul_assoc (star U.val), ← Matrix.mul_assoc,
      h₁, Matrix.one_mul, Matrix.mul_assoc, h₁, Matrix.mul_one] at hh
    rw [Matrix.mul_neg, Matrix.neg_mul] at hh
    exact (neg_eq_iff_eq_neg.mp hh.symm)

def logicalXAxisNormalizer : Subgroup (Matrix.unitaryGroup (Fin 2) ℂ) where
  carrier := {U | preservesXAxis U}
  one_mem' := Or.inl (by simp)
  mul_mem' := fun hU hV => X_axis_normalizer_mul _ _ hU hV
  inv_mem' := fun hU => X_axis_normalizer_inv _ hU

theorem preservesXAxis_of_projectivelyEquivalent (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (hUV : ProjectivelyEquivalent U.val V.val) (hV : preservesXAxis V) : preservesXAxis U := by
  have h := projectivelyEquivalent_conjugation_eq hUV SinglePauli.X.matrix
  change U.val * SinglePauli.X.matrix * star U.val =
      V.val * SinglePauli.X.matrix * star V.val at h
  unfold preservesXAxis at *
  rw [h]
  exact hV

def projectiveXAxisNormalizer : Subgroup (PU (Fin 2)) :=
  logicalXAxisNormalizer.map (projectiveMk (Fin 2))

private def quarterZ : Matrix.unitaryGroup (Fin 2) ℂ :=
  unitaryRotation SinglePauli.Z.matrix (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) (Real.pi / 4)

private theorem quarterZ_not_preserves : ¬ preservesXAxis quarterZ := by
  have hc : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have hs : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hval : quarterZ.val =
      Matrix.diagonal (fun j : Fin 2 =>
        if j = 0 then (↑(Real.sqrt 2 / 2) + Complex.I * ↑(Real.sqrt 2 / 2) : ℂ)
        else ↑(Real.sqrt 2 / 2) - Complex.I * ↑(Real.sqrt 2 / 2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [quarterZ, unitaryRotation, rotation, affine, SinglePauli.matrix,
        hc, hs, Matrix.diagonal_apply, Matrix.one_apply, sub_eq_add_neg]
  intro hp
  have hentry : (quarterZ.val * SinglePauli.X.matrix * star quarterZ.val) 0 1 = Complex.I := by
    rw [hval, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    let r : ℝ := Real.sqrt 2 / 2
    let c : ℂ := (r : ℂ)
    change ((if (0 : Fin 2) = 0 then c + Complex.I*c else c - Complex.I*c) *
      SinglePauli.X.matrix 0 1) *
      star (if (1 : Fin 2) = 0 then c + Complex.I*c else c - Complex.I*c) = Complex.I
    have hc' : star c = c := Complex.conj_ofReal r
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    norm_num [SinglePauli.matrix, map_sub, star_mul, hc', hI]
    have hsR : r * r = 1/2 := by
      have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      dsimp [r]
      nlinarith [h]
    have hsC : c * c = (1/2 : ℂ) := by
      change (r : ℂ) * (r : ℂ) = 1/2
      have hs := congrArg Complex.ofReal hsR
      simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hs
    have hsI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc
      _ = (c*c) + (Complex.I*Complex.I)*(c*c) + 2*Complex.I*(c*c) := by ring
      _ = _ := by rw [hsC, hsI]; ring
  rcases hp with hp | hp
  · have h := congrArg (fun M : Operator (Fin 2) => M 0 1) hp
    change _ = SinglePauli.X.matrix 0 1 at h
    rw [hentry] at h
    have hh := congrArg Complex.im h
    norm_num [SinglePauli.matrix] at hh
  · have h := congrArg (fun M : Operator (Fin 2) => M 0 1) hp
    change _ = -(SinglePauli.X.matrix 0 1) at h
    rw [hentry] at h
    have hh := congrArg Complex.im h
    norm_num [SinglePauli.matrix] at hh

theorem projectiveXAxisNormalizer_ne_top : projectiveXAxisNormalizer ≠ ⊤ := by
  intro h
  have hm : projectiveMk (Fin 2) quarterZ ∈ projectiveXAxisNormalizer := by rw [h]; trivial
  obtain ⟨U, hU, he⟩ := hm
  exact quarterZ_not_preserves (preservesXAxis_of_projectivelyEquivalent quarterZ U
    ((projectiveMk_eq_iff _ _ _).mp he.symm) hU)

theorem nativeExactDepth_lower_of_axis {n g q : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim 2 g) (d : ℕ)
    (haxis : ∀ h : ℕ, h < d → nativeLogicalImage C.encoding q h ⊆ projectiveXAxisNormalizer) :
    (d : ℕ∞) ≤ nativeExactDepth C.encoding q := by
  unfold nativeExactDepth positiveDepthInf
  apply le_sInf
  rintro _ ⟨h, hp, rfl, ht⟩
  apply ENat.natCast_le_natCast.mpr
  by_contra hlt
  have hh : Subgroup.closure (nativeLogicalImage C.encoding q h) ≤ projectiveXAxisNormalizer :=
    (Subgroup.closure_le _).mpr (haxis h (by omega))
  have htop : (⊤ : Subgroup (PU (Fin 2))) ≤ projectiveXAxisNormalizer := by
    change Subgroup.closure (nativeLogicalImage C.encoding q h) = ⊤ at ht
    rwa [ht] at hh
  exact projectiveXAxisNormalizer_ne_top (top_unique htop)

#print axioms logicalXAxisNormalizer
#print axioms projectiveXAxisNormalizer_ne_top
#print axioms nativeExactDepth_lower_of_axis

end

end CriticalDepth.FaultShorSaturation.BaconShor
