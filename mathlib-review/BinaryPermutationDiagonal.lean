import BinaryPermutationUnitary
import CSSCodePauliChecks

/-!
# Conjugating diagonal matrices by permutations
-/

namespace CriticalDepth.BinaryPermutationUnitary

open CriticalDepth.Manuscript Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem basisPermutation_conjugates_diagonal (e : Equiv.Perm ι) (f : ι → ℂ) :
    basisPermutation e * Matrix.diagonal f * (basisPermutation e).conjTranspose =
      Matrix.diagonal (fun x => f (e.symm x)) := by
  ext x y
  rw [basisPermutation_conjTranspose, Matrix.mul_assoc, basisPermutation_mul_apply, Matrix.diagonal_mul]
  rw [basisPermutation_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst y
    simp
  · have hn : e.symm x ≠ e.symm y := fun he => h (e.symm.injective he)
    simp [h, hn]

#print axioms basisPermutation_conjugates_diagonal

end CriticalDepth.BinaryPermutationUnitary

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation Matrix

theorem cssZMatrix_eq_diagonal {n : ℕ} (a : CSSWord n) :
    pauliMatrix 0 (cssZWord a) =
      Matrix.diagonal (fun x : QubitBasis n => cssSign (dotProduct (binaryWordEquiv n x) a)) := by
  classical
  ext x y
  have h := cssZWord_mulVec a (Pi.single y (1 : ℂ)) x
  have he : (pauliMatrix 0 (cssZWord a)).mulVec (Pi.single y (1 : ℂ)) x =
    pauliMatrix 0 (cssZWord a) x y := by rw [Matrix.mulVec_single_one]; rfl
  rw [he] at h
  rw [h, Matrix.diagonal_apply, Pi.single_apply]
  by_cases heq : x = y <;> simp [heq]

#print axioms cssZMatrix_eq_diagonal

end CriticalDepth.Manuscript20261114.CSSCode
