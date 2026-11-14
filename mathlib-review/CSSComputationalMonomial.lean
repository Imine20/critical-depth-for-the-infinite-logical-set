import CSSMonomial

/-!
# Monomial matrices from conjugates of the computational Z tests

The diagonal single-site signs distinguish all computational words.
A row of a unitary that intertwines those signs with diagonal operators
therefore has at most one nonzero entry.
-/

open scoped BigOperators

namespace CriticalDepth.CSSMonomial

open CriticalDepth.Manuscript Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugates of separating diagonal tests suffice for a monomial form. -/
theorem exists_monomial_of_separating_diagonal_conjugates
    (U : Operator ι) (hu : IsUnitary U)
    (z : α → ι → ℂ)
    (hsep : ∀ x y : ι, (∀ a, z a x = z a y) → x = y)
    (hdiag : ∀ (a : α) (x y : ι), x ≠ y →
      (U * diagonal (z a) * U.conjTranspose) x y = 0) :
    ∃ (f : Equiv.Perm ι) (phase : ι → ℂ),
      (∀ j, star (phase j) * phase j = 1) ∧
      ∀ x j, U x j = if x = f j then phase j else 0 := by
  classical
  let d (a : α) (x : ι) : ℂ := (U * diagonal (z a) * U.conjTranspose) x x
  have hD (a : α) : U * diagonal (z a) * U.conjTranspose = diagonal (d a) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      exact (diagonal_apply_eq _ _).symm
    · rw [hdiag a x y hxy, diagonal_apply_ne _ hxy]
  have hUU : U.conjTranspose * U = 1 := hu.1
  have hIntertwine (a : α) : diagonal (d a) * U = U * diagonal (z a) := by
    rw [← hD, Matrix.mul_assoc _ U.conjTranspose, hUU, Matrix.mul_one]
  have hEval (a : α) (x y : ι) (h : U x y ≠ 0) : d a x = z a y := by
    have he := congrArg (fun M : Operator ι => M x y) (hIntertwine a)
    change (diagonal (d a) * U) x y = (U * diagonal (z a)) x y at he
    rw [diagonal_mul, mul_diagonal, mul_comm (U x y)] at he
    exact mul_right_cancel₀ h he
  have hEntry (a b : ι) :
      (∑ t, U a t * star (U b t)) = (1 : Operator ι) a b :=
    congrFun (congrFun hu.2 a) b
  have hnz (x : ι) : ∃ y, U x y ≠ 0 := by
    by_contra! h
    have hh := hEntry x x
    simp [h] at hh
  choose g hg using hnz
  have huniq (x y : ι) (h : U x y ≠ 0) : y = g x := by
    apply hsep
    intro a
    exact (hEval a x y h).symm.trans (hEval a x (g x) (hg x))
  have hsparse (x y : ι) (h : y ≠ g x) : U x y = 0 := by
    by_contra hz
    exact h (huniq x y hz)
  have hsum (x x' : ι) :
      (∑ t, U x t * star (U x' t)) = U x (g x) * star (U x' (g x)) := by
    apply Finset.sum_eq_single (g x)
    · intro t _ ht
      rw [hsparse x t ht, zero_mul]
    · simp
  have hinj : Function.Injective g := by
    intro x x' h
    by_contra hne
    have he := hEntry x x'
    rw [hsum, Matrix.one_apply_ne hne] at he
    have hnz' : U x' (g x) ≠ 0 := h.symm ▸ hg x'
    exact (mul_ne_zero (hg x) (by simpa using hnz')) he
  let e := Equiv.ofBijective g ((Finite.injective_iff_bijective).mp hinj)
  refine ⟨e.symm, fun j => U (e.symm j) j, ?_, ?_⟩
  · intro j
    have he := hEntry (e.symm j) (e.symm j)
    have hg' : g (e.symm j) = j := e.apply_symm_apply j
    rw [hsum, hg', Matrix.one_apply_eq] at he
    exact (mul_comm _ _).trans he
  · intro x j
    by_cases hj : x = e.symm j
    · simp [hj]
    · have hne : j ≠ g x := fun h => hj (e.apply_eq_iff_eq_symm_apply.mp h.symm)
      rw [ite_eq_right hj, hsparse x j hne]

/-- The eigenvalue of the single-qubit Z matrix at the selected bit. -/
noncomputable def siteZSign {n : ℕ} (i : Fin n) (x : QubitBasis n) : ℂ :=
  if x i = 0 then 1 else -1

theorem singleSitePauli_z_eq_diagonal {n : ℕ} (i : Fin n) :
    pauliMatrix 0 (singleSitePauli i .Z) = diagonal (siteZSign i) := by
  classical
  ext x y
  rw [pauliMatrix_zero_eq_tensorEntries]
  change (∏ j, (singleSitePauli i .Z j).matrix (x j) (y j)) = _
  by_cases hxy : x = y
  · subst y
    rw [diagonal_apply_eq, Finset.prod_eq_single i]
    · have hz (a : Fin 2) : SinglePauli.Z.matrix a a = if a = 0 then 1 else -1 := by
        fin_cases a <;> norm_num [SinglePauli.matrix]
      simpa [singleSitePauli, siteZSign] using hz (x i)
    · intro j _ hj
      simp [singleSitePauli, hj, SinglePauli.matrix]
    · simp
  · rw [diagonal_apply_ne _ hxy]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra! h
      exact hxy (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    by_cases hji : j = i
    · subst j
      have hz (a b : Fin 2) (hab : a ≠ b) : SinglePauli.Z.matrix a b = 0 := by
        fin_cases a <;> fin_cases b <;> simp_all [SinglePauli.matrix]
      simpa [singleSitePauli] using hz (x i) (y i) hj
    · simp [singleSitePauli, hji, SinglePauli.matrix, Matrix.one_apply_ne hj]

/-- The physical unitary is monomial as soon as its conjugates of
single-site Z operators are diagonal in the computational basis. -/
theorem exists_monomial_of_singleSiteZ_conjugates {n : ℕ}
    (U : Operator (QubitBasis n)) (hu : IsUnitary U)
    (hdiag : ∀ (i : Fin n) (x y : QubitBasis n), x ≠ y →
      (U * pauliMatrix 0 (singleSitePauli i .Z) * U.conjTranspose) x y = 0) :
    ∃ (f : Equiv.Perm (QubitBasis n)) (phase : QubitBasis n → ℂ),
      (∀ j, star (phase j) * phase j = 1) ∧
      ∀ x j, U x j = if x = f j then phase j else 0 := by
  apply exists_monomial_of_separating_diagonal_conjugates U hu siteZSign
  · intro x y h
    funext i
    have he := h i
    unfold siteZSign at he
    have hbit : ∀ a b : Fin 2, (if a = 0 then (1 : ℂ) else -1) =
        (if b = 0 then 1 else -1) → a = b := by
      intro a b
      fin_cases a <;> fin_cases b <;> norm_num
    exact hbit _ _ he
  · intro i x y hxy
    simpa only [singleSitePauli_z_eq_diagonal] using hdiag i x y hxy

#print axioms exists_monomial_of_separating_diagonal_conjugates
#print axioms singleSitePauli_z_eq_diagonal
#print axioms exists_monomial_of_singleSiteZ_conjugates

end CriticalDepth.CSSMonomial
