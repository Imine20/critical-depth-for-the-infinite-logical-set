import FaultDiamondVariational
import FaultTraceNorm

/-!
For a difference of channels, the stabilized trace norm can be optimized
over density inputs even when its definition allows arbitrary matrices.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.FaultCPTPRepresentation
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem tensorIndex_amplify {R S : Type*} (e : R ≃ S)
    (L : MatrixChannel ι ι) (A : Matrix (S × ι) (S × ι) ℂ) :
    amplify L (A.submatrix (e.prodCongr (Equiv.refl ι)) (e.prodCongr (Equiv.refl ι))) =
      (amplify L A).submatrix (e.prodCongr (Equiv.refl ι)) (e.prodCongr (Equiv.refl ι)) := by
  ext p q
  rfl

private theorem amplify_conjTranspose {R : Type*} [Fintype R] [DecidableEq R]
    (L : MatrixChannel ι ι) (hL : IsCompletelyPositive L) (A : Matrix (R × ι) (R × ι) ℂ) :
    amplify L A.conjTranspose = (amplify L A).conjTranspose := by
  obtain ⟨K, rfl⟩ := exists_kraus_of_cp L hL
  have h (X : Matrix ι ι ℂ) : krausMap K X.conjTranspose = (krausMap K X).conjTranspose := by
    simp only [krausMap_apply, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  ext ⟨r, i⟩ ⟨s, j⟩
  exact congrFun (congrFun (h (Matrix.of fun a b => A (s, a) (r, b))) i) j

private theorem recoveredDifference_conjTranspose {R : Type*} [Fintype R] [DecidableEq R]
    (L : MatrixChannel ι ι) (hL : IsCompletelyPositive L) (A : Matrix (R × ι) (R × ι) ℂ) :
    amplify L A.conjTranspose - A.conjTranspose = (amplify L A - A).conjTranspose := by
  rw [Matrix.conjTranspose_sub, amplify_conjTranspose L hL]

theorem halfDiamond_bound_posSemidef_test {m : ℕ} (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L)
    (A E : Matrix (Fin m × ι) (Fin m × ι) ℂ) (hA : A.PosSemidef) (hE : IsEffect E) :
    |effectValue E (amplify L A - A)| ≤ A.trace.re * halfDiamondByEffects L := by
  by_cases hzero : A.trace.re = 0
  · have hA₀ : A = 0 := hA.trace_eq_zero_iff.mp (Complex.ext hzero
      (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm)
    subst A
    have hAmp : amplify L (0 : Matrix (Fin m × ι) (Fin m × ι) ℂ) = 0 := by
      ext a b
      change L 0 a.2 b.2 = 0
      simp
    simp [hAmp, effectValue]
  have hp : 0 < A.trace.re := lt_of_le_of_ne (Complex.nonneg_iff.mp hA.trace_nonneg).1 (Ne.symm hzero)
  let t := A.trace.re
  let X := (t⁻¹ : ℝ) • A
  have htr : A.trace = (t : ℂ) :=
    Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm)
  have hPos : IsDensity X := by
    refine ⟨hA.smul (inv_nonneg.mpr hp.le), ?_⟩
    change (((t⁻¹ : ℝ) : ℂ) • A).trace = 1
    rw [Matrix.trace_smul, htr, smul_eq_mul, Complex.ofReal_inv,
      inv_mul_cancel₀ (by exact_mod_cast hp.ne')]
  have hX : A = (t : ℂ) • X := by
    change A = (t : ℂ) • (((t⁻¹ : ℝ) : ℂ) • A)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hp.ne',
      Complex.ofReal_one, one_smul]
  have hAu : amplify L A - A = (t : ℂ) • (amplify L X - X) := by
    have hAmp : amplify L A = (t : ℂ) • amplify L X := by
      calc
        _ = amplify L ((t : ℂ) • X) := congrArg (amplify L) hX
        _ = amplify ((t : ℂ) • L) X := by
          ext a b
          change L ((t : ℂ) • (Matrix.of fun i j => X (a.1, i) (b.1, j))) a.2 b.2 = _
          rw [map_smul]
          rfl
        _ = _ := amplify_smul _ _ _
    exact (congrArg₂ Sub.sub hAmp hX).trans (smul_sub _ _ _).symm
  rw [hAu, effectValue_smul, abs_mul, abs_of_nonneg hp.le]
  exact mul_le_mul_of_nonneg_left (effect_test_le_halfDiamond L hCP hTP m X E hPos hE) hp.le

theorem traceNorm_amplifyDifference_bound_hermitian {m : ℕ} (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L)
    (A : Matrix (Fin m × ι) (Fin m × ι) ℂ) (hA : A.IsHermitian) :
    matrixTraceNorm (amplify L A - A) ≤ 2 * halfDiamondByEffects L * matrixTraceNorm A := by
  let P := A⁺
  let Q := A⁻
  have hP : P.PosSemidef := (CFC.posPart_nonneg A).posSemidef
  have hQ : Q.PosSemidef := (CFC.negPart_nonneg A).posSemidef
  have hD : A = P - Q := (CFC.posPart_sub_negPart A hA.isSelfAdjoint).symm
  have hT : matrixTraceNorm A = P.trace.re + Q.trace.re := by
    rw [matrixTraceNorm, ← CFC.posPart_add_negPart A hA.isSelfAdjoint, Matrix.trace_add, Complex.add_re]
  have hL : (amplify L A - A).IsHermitian := by
    change (amplify L A - A).conjTranspose = _
    rw [← recoveredDifference_conjTranspose L hCP, hA.eq]
  have hTr := densityDifference_trace_zero L hTP A
  obtain ⟨E, hE, hVal⟩ := (effect_diagonal_spectral_bound hL hTr).1
  have hEq :
      amplify L A - A = (amplify L P - P) - (amplify L Q - Q) := by
    nth_rw 1 2 [hD]
    have he : amplify L (P - Q) = amplify L P - amplify L Q := by
      ext i j
      change L (Matrix.of fun a b => P (i.1, a) (j.1, b) - Q (i.1, a) (j.1, b)) i.2 j.2 = _
      rw [show (Matrix.of fun a b => P (i.1, a) (j.1, b) - Q (i.1, a) (j.1, b)) =
        (Matrix.of fun a b => P (i.1, a) (j.1, b)) - (Matrix.of fun a b => Q (i.1, a) (j.1, b))
        from rfl, map_sub]
      rfl
    rw [he]
    abel
  have he := (abs_sub_le (effectValue E (amplify L P - P)) 0
    (effectValue E (amplify L Q - Q)))
  simp only [sub_zero, zero_sub, abs_neg] at he
  rw [matrixTraceNorm_eq_hermitianTraceNorm _ hL, hT]
  have hv : effectValue E (amplify L A - A) =
      effectValue E (amplify L P - P) - effectValue E (amplify L Q - Q) :=
    (congrArg (effectValue E) hEq).trans (effectValue_sub _ _ _)
  have hVal' := hVal.trans (congrArg abs hv)
  have h := he.trans (add_le_add (halfDiamond_bound_posSemidef_test L hCP hTP P E hP hE)
    (halfDiamond_bound_posSemidef_test L hCP hTP Q E hQ hE))
  rw [← hVal'] at h
  rw [← add_mul] at h
  linarith

private theorem hermitianDilation_amplifyDifference {m : ℕ} (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (A : Matrix (Fin m × ι) (Fin m × ι) ℂ) :
    let e := Equiv.sumProdDistrib (Fin m) (Fin m) ι
    let H := (hermitianDilation A).submatrix e e
    amplify L H - H = (hermitianDilation (amplify L A - A)).submatrix e e := by
  intro e H
  ext ⟨r, i⟩ ⟨s, j⟩
  have h₀ : Matrix.of (fun _ _ : ι => (0 : ℂ)) = (0 : Matrix ι ι ℂ) := rfl
  cases r with
  | inl r =>
    cases s with
    | inl s => simp [e, H, hermitianDilation, amplify, h₀]
    | inr s => rfl
  | inr r =>
    cases s with
    | inl s =>
      change amplify L A.conjTranspose (r, i) (s, j) - A.conjTranspose (r, i) (s, j) =
        (amplify L A - A).conjTranspose (r, i) (s, j)
      exact congrFun (congrFun (recoveredDifference_conjTranspose L hCP A) (r, i)) (s, j)
    | inr s => simp [e, H, hermitianDilation, amplify, h₀]

theorem traceNorm_amplifyDifference_bound {m : ℕ} (L : MatrixChannel ι ι)
    (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L)
    (A : Matrix (Fin m × ι) (Fin m × ι) ℂ) :
    matrixTraceNorm (amplify L A - A) ≤ 2 * halfDiamondByEffects L * matrixTraceNorm A := by
  let e₁ := Equiv.sumProdDistrib (Fin m) (Fin m) ι
  let r := Fintype.equivFin (Fin m ⊕ Fin m)
  let e₂ := r.symm.prodCongr (Equiv.refl ι)
  let X := (hermitianDilation A).submatrix e₁ e₁
  let Y := X.submatrix e₂ e₂
  have hy : Y.IsHermitian := ((hermitianDilation_isHermitian A).submatrix e₁).submatrix e₂
  have he :
      amplify L Y - Y = ((hermitianDilation (amplify L A - A)).submatrix e₁ e₁).submatrix e₂ e₂ := by
    rw [show Y = X.submatrix e₂ e₂ from rfl, tensorIndex_amplify r.symm]
    change ((amplify L X - X).submatrix e₂ e₂) = _
    rw [hermitianDilation_amplifyDifference L hCP A]
  have h := traceNorm_amplifyDifference_bound_hermitian L hCP hTP Y hy
  rw [he] at h
  dsimp only [Y, X] at h
  simp only [matrixTraceNorm_submatrix_equiv, matrixTraceNorm_hermitianDilation] at h
  nlinarith only [h]

def halfCompletelyBoundedTraceNorm (L : MatrixChannel ι ι) : ℝ :=
  sSup {p | ∃ (m : ℕ) (A : Matrix (Fin m × ι) (Fin m × ι) ℂ),
    matrixTraceNorm A ≤ 1 ∧ p = matrixTraceNorm (amplify L A - A) / 2}

theorem halfDiamondByEffects_eq_halfCompletelyBoundedTraceNorm
    (L : MatrixChannel ι ι) (hCP : IsCompletelyPositive L) (hTP : IsTracePreserving L) :
    halfDiamondByEffects L = halfCompletelyBoundedTraceNorm L := by
  let S : Set ℝ := {p | ∃ (m : ℕ) (A : Matrix (Fin m × ι) (Fin m × ι) ℂ),
    matrixTraceNorm A ≤ 1 ∧ p = matrixTraceNorm (amplify L A - A) / 2}
  have h₀ : 0 ≤ halfDiamondByEffects L := Real.sSup_nonneg (by
    rintro _ ⟨_, _, _, _, _, rfl⟩
    exact abs_nonneg _)
  have hb : ∀ p ∈ S, p ≤ halfDiamondByEffects L := by
    rintro _ ⟨m, A, hA, rfl⟩
    have h := traceNorm_amplifyDifference_bound L hCP hTP A
    have hh := h.trans (mul_le_of_le_one_right (mul_nonneg (by norm_num) h₀) hA)
    linarith
  have hB : BddAbove S := ⟨_, hb⟩
  apply le_antisymm
  · rw [halfDiamondByEffects_eq_halfStabilizedTraceDistance L hCP hTP]
    apply real_sSup_le_of_nonneg
    · rintro _ ⟨m, A, hA, rfl⟩
      apply le_csSup hB
      refine ⟨m, A, ?_, ?_⟩
      · rw [matrixTraceNorm, CFC.abs_of_nonneg A hA.1.nonneg, hA.2, Complex.one_re]
      · rw [matrixTraceNorm_eq_hermitianTraceNorm _ (densityDifference_hermitian L hCP A hA)]
    · apply Real.sSup_nonneg
      rintro _ ⟨_, A, _, rfl⟩
      exact div_nonneg (matrixTraceNorm_nonneg (amplify L A - A)) (by norm_num)
  · exact real_sSup_le_of_nonneg hb h₀

#print axioms traceNorm_amplifyDifference_bound
#print axioms halfDiamondByEffects_eq_halfCompletelyBoundedTraceNorm

end
end CriticalDepth.FaultChannelEffects
