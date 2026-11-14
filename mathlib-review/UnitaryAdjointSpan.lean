import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

/-!
# Real span of unitary conjugates of a skew-Hermitian matrix

A real submodule invariant under unitary conjugation and containing the
identity and one nonscalar Hermitian matrix contains every Hermitian matrix.
The proof uses spectral diagonalization and differences of diagonal matrix
units obtained by swapping unequal eigenvalues. Multiplication by the
imaginary unit gives the skew-Hermitian statement.
-/

open scoped BigOperators
open Unitary

namespace CriticalDepth.UnitaryAdjointSpan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Mat (ι : Type*) := Matrix ι ι ℂ

abbrev conj (U : Matrix.unitaryGroup ι ℂ) (A : Mat ι) : Mat ι :=
  conjStarAlgAut ℂ (Mat ι) U A

def ConjugationInvariant (E : Submodule ℝ (Mat ι)) : Prop :=
  ∀ U : Matrix.unitaryGroup ι ℂ, ∀ A ∈ E, conj U A ∈ E

private def swapUnitary (i j : ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.swap ℂ i j, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_swap, Matrix.swap_mul_self]⟩

private theorem conj_swap_diagonal (f : ι → ℂ) (i j : ι) :
    conj (swapUnitary i j) (Matrix.diagonal f) =
      Matrix.diagonal (f ∘ Equiv.swap i j) := by
  change Matrix.swap ℂ i j * Matrix.diagonal f * star (Matrix.swap ℂ i j) = _
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_swap]
  simp only [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  simpa only [Matrix.submatrix_submatrix, Equiv.symm_swap, Function.comp_id,
    Function.id_comp] using (Matrix.submatrix_diagonal_equiv f (Equiv.swap i j))

private def diagonalUnit (i : ι) : Mat ι :=
  Matrix.diagonal (Pi.single i 1)

private theorem diag_unit_sub_scaled (f : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    Matrix.diagonal (fun k => (f k : ℂ)) -
        Matrix.diagonal ((fun k => (f k : ℂ)) ∘ Equiv.swap i j) =
      (f i - f j) • (diagonalUnit i - diagonalUnit j) := by
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases hai : a = i
    · subst a
      simp [diagonalUnit, Pi.single_apply, hij, RCLike.real_smul_eq_coe_mul]
    · by_cases haj : a = j
      · subst a
        simp [diagonalUnit, Pi.single_apply, hai, hij, RCLike.real_smul_eq_coe_mul]
        <;> ring
      · simp [diagonalUnit, Pi.single_apply, hai, haj, Equiv.swap_apply_of_ne_of_ne hai haj]
  · simp [diagonalUnit, Matrix.diagonal_apply_ne _ hab]

private theorem diag_unit_difference_mem (E : Submodule ℝ (Mat ι))
    (hE : ConjugationInvariant E) (f : ι → ℝ)
    (hf : Matrix.diagonal (fun k => (f k : ℂ)) ∈ E)
    (i j : ι) (hne : f i ≠ f j) : diagonalUnit i - diagonalUnit j ∈ E := by
  have hij : i ≠ j := fun h => hne (congrArg f h)
  have h := E.sub_mem hf (hE (swapUnitary i j) _ hf)
  rw [conj_swap_diagonal (fun k => (f k : ℂ)) i j, diag_unit_sub_scaled f i j hij] at h
  have hinv := E.smul_mem (f i - f j)⁻¹ h
  simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] using hinv

private theorem all_diag_unit_differences_mem (E : Submodule ℝ (Mat ι))
    (hE : ConjugationInvariant E) (f : ι → ℝ)
    (hf : Matrix.diagonal (fun k => (f k : ℂ)) ∈ E)
    {p q : ι} (hpq : f p ≠ f q) (i j : ι) :
    diagonalUnit i - diagonalUnit j ∈ E := by
  by_cases hij : f i = f j
  · have bridge (k : ι) (hik : f i ≠ f k) : diagonalUnit i - diagonalUnit j ∈ E := by
      have hjk : f j ≠ f k := hij ▸ hik
      have hi := diag_unit_difference_mem E hE f hf i k hik
      have hj := diag_unit_difference_mem E hE f hf j k hjk
      convert E.sub_mem hi hj using 1 <;> abel
    by_cases hip : f i = f p
    · exact bridge q (fun h => hpq (hip.symm.trans h))
    · exact bridge p hip
  · exact diag_unit_difference_mem E hE f hf i j hij

private theorem sum_diag_units : ∑ i : ι, diagonalUnit i = (1 : Mat ι) := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Matrix.sum_apply, diagonalUnit, Pi.single_apply, Finset.sum_ite_eq']
  · simp [Matrix.sum_apply, diagonalUnit, Matrix.diagonal_apply_ne _ hab, Matrix.one_apply, hab]

private theorem all_diag_units_mem (E : Submodule ℝ (Mat ι)) (hone : (1 : Mat ι) ∈ E)
    (hdiffs : ∀ i j : ι, diagonalUnit i - diagonalUnit j ∈ E) (i : ι) :
    diagonalUnit i ∈ E := by
  have hsum : (∑ j : ι, (diagonalUnit i - diagonalUnit j)) ∈ E :=
    E.sum_mem (fun j _ => hdiffs i j)
  have hscaled : (Fintype.card ι : ℝ) • diagonalUnit i ∈ E := by
    have h := E.add_mem hsum hone
    rw [Finset.sum_sub_distrib, sum_diag_units, sub_add_cancel,
      Finset.sum_const, Finset.card_univ] at h
    simpa only [Nat.cast_smul_eq_nsmul] using h
  letI : Nonempty ι := ⟨i⟩
  have hcard : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  simpa only [smul_smul, inv_mul_cancel₀ hcard, one_smul] using
    E.smul_mem (Fintype.card ι : ℝ)⁻¹ hscaled

private theorem diag_real_mem (E : Submodule ℝ (Mat ι))
    (hunits : ∀ i : ι, diagonalUnit i ∈ E) (f : ι → ℝ) :
    Matrix.diagonal (fun i => (f i : ℂ)) ∈ E := by
  classical
  have hsum : (∑ i : ι, f i • diagonalUnit i) ∈ E :=
    E.sum_mem (fun i _ => E.smul_mem (f i) (hunits i))
  have heq : Matrix.diagonal (fun i => (f i : ℂ)) = ∑ i : ι, f i • diagonalUnit i := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [Matrix.sum_apply, diagonalUnit, Pi.single_apply, RCLike.real_smul_eq_coe_mul,
        Finset.sum_ite_eq', mul_ite]
    · simp [Matrix.sum_apply, diagonalUnit, Matrix.diagonal_apply_ne _ hab]
  exact heq.symm ▸ hsum

/-- A nonscalar Hermitian vector and the identity generate all Hermitians
in any conjugation-invariant real submodule. -/
theorem hermitian_mem_of_invariant (E : Submodule ℝ (Mat ι))
    (hE : ConjugationInvariant E) (hone : (1 : Mat ι) ∈ E)
    (H : Mat ι) (hH : H.IsHermitian) (hmem : H ∈ E)
    (hnonscalar : ¬ ∃ c : ℂ, H = c • (1 : Mat ι))
    (A : Mat ι) (hA : A.IsHermitian) : A ∈ E := by
  classical
  let f := hH.eigenvalues
  have hf : Matrix.diagonal (fun i => (f i : ℂ)) ∈ E := by
    have h := hE (star hH.eigenvectorUnitary) H hmem
    have hC : conj (star hH.eigenvectorUnitary) H =
        Matrix.diagonal (fun i => (f i : ℂ)) := hH.conjStarAlgAut_star_eigenvectorUnitary
    exact hC ▸ h
  have hpair : ∃ i j : ι, f i ≠ f j := by
    by_contra! hconst
    cases isEmpty_or_nonempty ι with
    | inl hempty =>
      apply hnonscalar
      exact ⟨0, Subsingleton.elim _ _⟩
    | inr hnonempty =>
      let i := Classical.choice hnonempty
      have hdiag : Matrix.diagonal (fun j => (f j : ℂ)) = (f i : ℂ) • (1 : Mat ι) := by
        rw [Matrix.smul_one_eq_diagonal]
        congr 1
        funext j
        rw [hconst j i]
      apply hnonscalar
      refine ⟨(f i : ℂ), ?_⟩
      calc
        H = conj hH.eigenvectorUnitary (Matrix.diagonal (fun j => (f j : ℂ))) :=
          hH.spectral_theorem
        _ = (f i : ℂ) • (1 : Mat ι) := by
          rw [hdiag]
          exact (map_smul (conjStarAlgAut ℂ (Mat ι) hH.eigenvectorUnitary)
            (f i : ℂ) (1 : Mat ι)).trans (by rw [map_one])
  obtain ⟨p, q, hpq⟩ := hpair
  have hunits := all_diag_units_mem E hone (all_diag_unit_differences_mem E hE f hf hpq)
  rw [hA.spectral_theorem]
  exact hE hA.eigenvectorUnitary _ (diag_real_mem E hunits hA.eigenvalues)


/-- The corresponding result in the tangent space of the unitary group. -/
theorem skew_mem_of_invariant (E : Submodule ℝ (Mat ι))
    (hE : ConjugationInvariant E) (hscalar : Complex.I • (1 : Mat ι) ∈ E)
    (X : Mat ι) (hX : star X = -X) (hmem : X ∈ E)
    (hnonscalar : ¬ ∃ c : ℂ, X = c • (1 : Mat ι))
    (Y : Mat ι) (hY : star Y = -Y) : Y ∈ E := by
  let mulI : Mat ι →ₗ[ℝ] Mat ι :=
    { toFun := fun A => Complex.I • A
      map_add' := fun A B => smul_add Complex.I A B
      map_smul' := fun r A => smul_comm Complex.I r A }
  let EH := E.comap mulI
  have hEH : ConjugationInvariant EH := by
    intro U A hA
    change Complex.I • A ∈ E at hA
    change Complex.I • conj U A ∈ E
    simpa only [map_smul] using hE U (Complex.I • A) hA
  have hI : star Complex.I = -Complex.I := by simp
  have hII : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  have hHermitian (A : Mat ι) (hA : star A = -A) :
      ((-Complex.I) • A).IsHermitian := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    change star ((-Complex.I) • A) = (-Complex.I) • A
    rw [star_smul, star_neg, hI, neg_neg, hA, smul_neg, neg_smul]
  have hXH : (-Complex.I) • X ∈ EH := by
    change Complex.I • ((-Complex.I) • X) ∈ E
    simpa only [smul_smul, hII, one_smul] using hmem
  have hXn : ¬ ∃ c : ℂ, (-Complex.I) • X = c • (1 : Mat ι) := by
    rintro ⟨c, hc⟩
    apply hnonscalar
    refine ⟨Complex.I * c, ?_⟩
    have h := congrArg (fun A : Mat ι => Complex.I • A) hc
    simpa only [smul_smul, hII, one_smul] using h
  have result := hermitian_mem_of_invariant EH hEH hscalar ((-Complex.I) • X)
    (hHermitian X hX) hXH hXn ((-Complex.I) • Y) (hHermitian Y hY)
  change Complex.I • ((-Complex.I) • Y) ∈ E at result
  simpa only [smul_smul, hII, one_smul] using result

/-- The real span of the unitary conjugacy orbit and the scalar phase velocity. -/
noncomputable def conjugatesAndPhaseSpan (X : Mat ι) : Submodule ℝ (Mat ι) :=
  Submodule.span ℝ (insert (Complex.I • (1 : Mat ι))
    (Set.range fun U : Matrix.unitaryGroup ι ℂ => conj U X))

theorem conjugatesAndPhaseSpan_invariant (X : Mat ι) :
    ConjugationInvariant (conjugatesAndPhaseSpan X) := by
  intro U A hA
  induction hA using Submodule.span_induction with
  | mem B hB =>
    rcases Set.mem_insert_iff.mp hB with hscalar | hconj
    · subst B
      have hphase : conj U (Complex.I • (1 : Mat ι)) = Complex.I • (1 : Mat ι) := by
        exact (map_smul (conjStarAlgAut ℂ (Mat ι) U) Complex.I (1 : Mat ι)).trans
          (by rw [map_one])
      rw [hphase]
      exact Submodule.subset_span (Set.mem_insert _ _)
    · obtain ⟨V, rfl⟩ := hconj
      change conj U (conj V X) ∈ conjugatesAndPhaseSpan X
      rw [← show conj (U * V) X = conj U (conj V X) from
        conjStarAlgAut_mul_apply (S := ℂ) U V X]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨U * V, rfl⟩)
  | zero => simpa only [map_zero] using (conjugatesAndPhaseSpan X).zero_mem
  | add _ _ _ _ h1 h2 => simpa only [map_add] using (conjugatesAndPhaseSpan X).add_mem h1 h2
  | smul r B _ hB =>
    have hsmul : conj U (r • B) = r • conj U B := by
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    rw [hsmul]
    exact (conjugatesAndPhaseSpan X).smul_mem r hB

/-- The orbit plus the scalar phase yields the full real skew-Hermitian subspace. -/
theorem conjugatesAndPhaseSpan_eq_skewAdjoint (X : Mat ι) (hX : star X = -X)
    (hnonscalar : ¬ ∃ c : ℂ, X = c • (1 : Mat ι)) :
    conjugatesAndPhaseSpan X = skewAdjoint.submodule ℝ (Mat ι) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with hscalar | hconj
    · subst A
      change star (Complex.I • (1 : Mat ι)) = -(Complex.I • (1 : Mat ι))
      have hI : star Complex.I = -Complex.I := by simp
      rw [star_smul, hI, star_one, neg_smul]
    · obtain ⟨U, rfl⟩ := hconj
      change star (conj U X) = -conj U X
      rw [← map_star, hX, map_neg]
  · intro Y hY
    have hscalar : Complex.I • (1 : Mat ι) ∈ conjugatesAndPhaseSpan X :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hmem : X ∈ conjugatesAndPhaseSpan X := by
      apply Submodule.subset_span
      refine Set.mem_insert_of_mem _ ⟨1, ?_⟩
      simp
    exact skew_mem_of_invariant (conjugatesAndPhaseSpan X) (conjugatesAndPhaseSpan_invariant X)
      hscalar X hX hmem hnonscalar Y hY

#print axioms hermitian_mem_of_invariant
#print axioms skew_mem_of_invariant
#print axioms conjugatesAndPhaseSpan_eq_skewAdjoint

end CriticalDepth.UnitaryAdjointSpan
