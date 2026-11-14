import FaultChannelEffects

/-!
For a traceless Hermitian matrix the range of measurement-bias values
has maximum equal to half the sum of the absolute eigenvalues.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hermitianTraceNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

theorem effect_diagonal_spectral_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (htr : A.trace = 0) :
    IsGreatest {t : ℝ | ∃ E : Matrix ι ι ℂ, IsEffect E ∧ t = |effectValue E A|}
      (hermitianTraceNorm A hA / 2) := by
  classical
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let spectrumValues := hA.eigenvalues
  have hu₁ : U.conjTranspose * U = 1 := (Unitary.mem_iff.mp hA.eigenvectorUnitary.property).1
  have hu₂ : U * U.conjTranspose = 1 := (Unitary.mem_iff.mp hA.eigenvectorUnitary.property).2
  have hSpec : A = U * Matrix.diagonal (fun i => (spectrumValues i : ℂ)) * U.conjTranspose := by
    simpa only [U, spectrumValues, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hA.spectral_theorem
  have hsum : ∑ i, spectrumValues i = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [htr] at h
    have h' : 0 = ∑ i, spectrumValues i := by
      simpa [spectrumValues, ← Complex.ofReal_sum] using congrArg Complex.re h
    exact h'.symm
  have hD (E : Matrix ι ι ℂ) :
      effectValue E A = ∑ i, ((U.conjTranspose * E * U) i i).re * spectrumValues i := by
    unfold effectValue
    nth_rw 1 [hSpec]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ U.conjTranspose]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  let pos := ∑ i : ι, max (spectrumValues i) 0
  let neg := ∑ i : ι, min (spectrumValues i) 0
  have hPN : pos + neg = 0 := by
    dsimp [pos, neg]
    rw [← Finset.sum_add_distrib]
    have h : (∑ i, (max (spectrumValues i) 0 + min (spectrumValues i) 0)) =
        ∑ i, spectrumValues i := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [add_zero] using max_add_min (spectrumValues i) 0
    exact h.trans hsum
  have hnorm : hermitianTraceNorm A hA = pos - neg := by
    unfold hermitianTraceNorm
    dsimp [pos, neg, spectrumValues]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ hA.eigenvalues i
    · simp [abs_of_nonneg hi, max_eq_left hi, min_eq_right hi]
    · have hl := le_of_not_ge hi
      simp [abs_of_nonpos hl, max_eq_right hl, min_eq_left hl]
  have hHalf : hermitianTraceNorm A hA / 2 = pos := by linarith
  rw [hHalf]
  refine ⟨?_, ?_⟩
  · let D := Matrix.diagonal (fun i => if 0 ≤ spectrumValues i then (1 : ℂ) else 0)
    let E := U * D * U.conjTranspose
    have hpD : D.PosSemidef := Matrix.PosSemidef.diagonal (fun i => by split <;> simp)
    have hcD : (1 - D).PosSemidef := by
      have hh : (1 - D) = Matrix.diagonal (fun i => if 0 ≤ spectrumValues i then (0 : ℂ) else 1) := by
        ext i j
        by_cases hij : i = j
        · subst j
          by_cases hi : 0 ≤ spectrumValues i <;> simp [D, hi]
        · simp [D, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      rw [hh]
      exact Matrix.PosSemidef.diagonal (fun i => by split <;> simp)
    have he : IsEffect E := by
      refine ⟨hpD.mul_mul_conjTranspose_same U, ?_⟩
      have hEq : 1 - E = U * (1 - D) * U.conjTranspose := by
        simp only [E, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hu₂]
      rw [hEq]
      exact hcD.mul_mul_conjTranspose_same U
    refine ⟨E, he, ?_⟩
    have hs : U.conjTranspose * E * U = D := by
      dsimp [E]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu₁, Matrix.one_mul,
        Matrix.mul_assoc, hu₁, Matrix.mul_one]
    have hv : effectValue E A = pos := by
      rw [hD E, hs]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [D]
      rw [Matrix.diagonal_apply_eq]
      by_cases hi : 0 ≤ spectrumValues i
      · simp [D, hi, max_eq_left hi]
      · simp [D, hi, max_eq_right (le_of_not_ge hi)]
    rw [hv, abs_of_nonneg]
    exact Finset.sum_nonneg fun i _ => le_max_right _ _
  · rintro _ ⟨E, hE, rfl⟩
    let T := U.conjTranspose * E * U
    have hT : T.PosSemidef := hE.1.conjTranspose_mul_mul_same U
    have hTc : (1 - T).PosSemidef := by
      have ht : 1 - T = U.conjTranspose * (1 - E) * U := by
        simp only [T, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hu₁]
      rw [ht]
      exact hE.2.conjTranspose_mul_mul_same U
    have hdiag (i : ι) : 0 ≤ (T i i).re ∧ (T i i).re ≤ 1 := by
      have h := (Complex.nonneg_iff.mp (hT.diag_nonneg (i := i))).1
      have hc := (Complex.nonneg_iff.mp (hTc.diag_nonneg (i := i))).1
      change 0 ≤ ((1 - T) i i).re at hc
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at hc
      exact ⟨h, by linarith⟩
    have hi (i : ι) : min (spectrumValues i) 0 ≤ (T i i).re * spectrumValues i ∧ (T i i).re * spectrumValues i ≤ max (spectrumValues i) 0 := by
      obtain ⟨h₀, h₁⟩ := hdiag i
      by_cases heig : 0 ≤ spectrumValues i
      · rw [min_eq_right heig, max_eq_left heig]
        exact ⟨mul_nonneg h₀ heig, by simpa using mul_le_mul_of_nonneg_right h₁ heig⟩
      · have hl := le_of_not_ge heig
        rw [min_eq_left hl, max_eq_right hl]
        exact ⟨by simpa using mul_le_mul_of_nonpos_right h₁ hl, mul_nonpos_of_nonneg_of_nonpos h₀ hl⟩
    have hm := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (hi i).1)
    have hM := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (hi i).2)
    rw [hD E, abs_le]
    exact ⟨by change neg ≤ _ at hm; linarith, hM⟩

#print axioms effect_diagonal_spectral_bound

end

end CriticalDepth.FaultChannelEffects