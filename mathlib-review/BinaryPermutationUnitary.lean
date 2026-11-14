import CriticalDepthMathlib
import FaultShorEncoding
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# From reversible maps on basis strings to physical permutation gates

A basis equivalence gives a unitary that maps each computational basis
state to its image. The locality condition below describes a genuine
tensor-local action, by requiring the complement to stay unchanged
and the selected output coordinates to depend only on the selected inputs.
-/

namespace CriticalDepth.BinaryPermutationUnitary

open Manuscript
open Matrix

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The column indexed by y is the coordinate vector at e y. -/
def basisPermutation (e : Equiv.Perm β) : Matrix β β ℂ :=
  Equiv.Perm.permMatrix ℂ e.symm

omit [Fintype β] in
theorem basisPermutation_apply (e : Equiv.Perm β) (x y : β) :
    basisPermutation e x y = if x = e y then 1 else 0 := by
  simp [basisPermutation, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.symm_apply_eq]


/-- Left multiplication by a permutation relabels rows by the inverse map. -/
theorem basisPermutation_mul_apply {κ : Type*} (e : Equiv.Perm β)
    (A : Matrix β κ ℂ) (x : β) (j : κ) :
    (basisPermutation e * A) x j = A (e.symm x) j := by
  unfold basisPermutation
  exact congrArg (fun M : Matrix β κ ℂ => M x j)
    (PEquiv.toMatrix_toPEquiv_mul e.symm A)

theorem basisPermutation_mul (e f : Equiv.Perm β) :
    basisPermutation e * basisPermutation f = basisPermutation (f.trans e) := by
  ext x y
  rw [basisPermutation_mul_apply, basisPermutation_apply, basisPermutation_apply]
  rw [Equiv.trans_apply]
  by_cases h : x = e (f y)
  · subst x
    simp
  · have hn : e.symm x ≠ f y := fun he => h ((e.apply_symm_apply x).symm.trans (congrArg e he))
    simp [h, hn]

omit [Fintype β] in
theorem basisPermutation_conjTranspose (e : Equiv.Perm β) :
    (basisPermutation e).conjTranspose = basisPermutation e.symm := by
  ext x y
  rw [Matrix.conjTranspose_apply, basisPermutation_apply, basisPermutation_apply]
  by_cases h : y = e x
  · have he : x = e.symm y := by rw [h, e.symm_apply_apply]
    simp only [ite_eq_left h, ite_eq_left he, star_one]
  · have he : x ≠ e.symm y := fun hx => h ((e.apply_symm_apply y).symm.trans
        (congrArg e hx).symm)
    simp only [ite_eq_right h, ite_eq_right he, star_zero]

theorem basisPermutation_isUnitary (e : Equiv.Perm β) :
    IsUnitary (basisPermutation e) := by
  have hId : basisPermutation (Equiv.refl β) = 1 := by
    ext x y
    rw [basisPermutation_apply, Equiv.refl_apply]
    by_cases h : x = y
    · subst y
      rw [Matrix.one_apply_eq]
      exact ite_eq_left rfl
    · rw [Matrix.one_apply_ne h]
      exact ite_eq_right h
  unfold IsUnitary
  simp only [Matrix.star_eq_conjTranspose, basisPermutation_conjTranspose, basisPermutation_mul]
  have hLeft : e.trans e.symm = Equiv.refl β := by
    apply Equiv.ext
    exact e.symm_apply_apply
  have hRight : e.symm.trans e = Equiv.refl β := by
    apply Equiv.ext
    exact e.apply_symm_apply
  exact ⟨by rw [hLeft, hId], by rw [hRight, hId]⟩

/-- An exact criterion for permutation gates acting on a rectangular tensor support. -/
theorem basisPermutation_supportedOn {n : ℕ} {dim : Fin n → ℕ}
    (S : Finset (Fin n)) (e : Equiv.Perm (PhysicalBasis n dim))
    (localMap : Equiv.Perm (LocalBasis dim S))
    (hout : ∀ x i, i ∉ S → e x i = x i)
    (hin : ∀ x, (fun i : S => e x i.val) = localMap (fun i : S => x i.val)) :
    SupportedOn (basisPermutation e) S := by
  classical
  refine ⟨basisPermutation localMap, ?_⟩
  ext x y
  rw [basisPermutation_apply]
  unfold localEmbed
  by_cases hOut : ∀ i, i ∉ S → x i = y i
  · simp only [basisPermutation_apply]
    have hEq : x = e y ↔ (fun i : S => x i.val) = localMap (fun i : S => y i.val) := by
      constructor
      · intro h
        rw [h]
        exact hin y
      · intro h
        rw [← hin y] at h
        funext i
        by_cases hi : i ∈ S
        · exact congrFun h ⟨i, hi⟩
        · rw [hout y i hi]
          exact hOut i hi
    by_cases h : x = e y
    · simp only [ite_eq_left h, ite_eq_left hOut, ite_eq_left (hEq.mp h)]
    · have hn : ¬ (fun i : S => x i.val) = localMap (fun i : S => y i.val) :=
        fun he => h (hEq.mpr he)
      simp only [ite_eq_right h, ite_eq_left hOut, ite_eq_right hn]
  · have hNe : x ≠ e y := by
      intro h
      apply hOut
      rw [h]
      exact hout y
    simp only [ite_eq_right hOut, ite_eq_right hNe]

section Binary

open CriticalDepth.FaultShorSaturation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Translation of a binary word, i.e. the action of its unphased X mask. -/
def translate (a : ι → Bit) : Equiv.Perm (ι → Bit) where
  toFun x := x + a
  invFun x := x - a
  left_inv x := add_sub_cancel_right x a
  right_inv x := sub_add_cancel x a

/-- Conjugation carries a translation by a binary mask to the translation
by its image under the linear reversible transformation. -/
theorem linearPermutation_conjugates_translate
    (L : (ι → Bit) ≃ₗ[Bit] (ι → Bit)) (a : ι → Bit) :
    basisPermutation L.toEquiv * basisPermutation (translate a) *
      (basisPermutation L.toEquiv).conjTranspose =
        basisPermutation (translate (L a)) := by
  rw [basisPermutation_conjTranspose, basisPermutation_mul, basisPermutation_mul]
  apply congrArg basisPermutation
  apply Equiv.ext
  intro x
  change L (L.symm x + a) = x + L a
  rw [map_add, LinearEquiv.apply_symm_apply]

/-- A basis equivalence preserving row parities fixes both columns of the
concrete rectangular Shor encoding. -/
theorem rowParityPreserving_permutation_fixes_shorEncoding {rows columns : ℕ}
    (e : Equiv.Perm (Mask rows (columns + 1)))
    (hparity : ∀ x i, rowParity (e x) i = rowParity x i) :
    basisPermutation e * shorEncoding rows columns = shorEncoding rows columns := by
  classical
  ext x b
  rw [basisPermutation_mul_apply]
  have hmem : e.symm x ∈ parityWords b ↔ x ∈ parityWords b := by
    rw [parityWords_mem_iff, parityWords_mem_iff]
    have h (i : Fin rows) : rowParity x i = rowParity (e.symm x) i := by
      simpa only [Equiv.apply_symm_apply] using hparity (e.symm x) i
    simp_rw [h]
  simp only [shorEncoding, hmem]

end Binary

#print axioms basisPermutation_isUnitary
#print axioms basisPermutation_supportedOn
#print axioms linearPermutation_conjugates_translate
#print axioms rowParityPreserving_permutation_fixes_shorEncoding

end CriticalDepth.BinaryPermutationUnitary
