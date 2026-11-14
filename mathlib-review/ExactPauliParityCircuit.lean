import ExactControlProjector
import BinaryPermutationUnitary

/-!
# Exact parity computation for a tensor Z rotation
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped BigOperators

noncomputable section

variable {k : ℕ}

/-- A CNOT with control c and target t on computational basis words. -/
def cnotWord (c t : Fin k) (hct : c ≠ t) : Equiv.Perm (QubitBasis k) :=
  have hInv : Function.Involutive (fun x : QubitBasis k => Function.update x t
      (if x c = 0 then x t else if x t = 0 then 1 else 0)) := by
    intro x
    funext i
    by_cases hi : i = t
    · subst i
      by_cases h : x c = 0
      · simp [Function.update_of_ne hct, h]
      · have hBit (b : Fin 2) : b = 0 ∨ b = 1 := by fin_cases b <;> simp
        rcases hBit (x t) with ht | ht <;> simp [Function.update_of_ne hct, h, ht]
    · simp [hi]
  hInv.toPerm _

theorem cnotWord_at_target (c t : Fin k) (hct : c ≠ t) (x : QubitBasis k) :
    cnotWord c t hct x t = if x c = 0 then x t else if x t = 0 then 1 else 0 := by
  unfold cnotWord
  exact Function.update_self _ _ _

theorem cnotWord_else (c t : Fin k) (hct : c ≠ t) (x : QubitBasis k)
    {i : Fin k} (hi : i ≠ t) : cnotWord c t hct x i = x i := by
  unfold cnotWord
  exact Function.update_of_ne hi _ _

/-- Compute all prescribed control parity into the target by ordered CNOTs. -/
def cnotParityWord (t : Fin k) : (L : List (Fin k)) → (∀ c ∈ L, c ≠ t) →
    Equiv.Perm (QubitBasis k)
  | [], _ => 1
  | c :: tail, h =>
    cnotWord c t (h c (List.mem_cons_self ..)) *
      cnotParityWord t tail (fun a ha => h a (List.mem_cons_of_mem c ha))

private theorem cnotBitSign (a b : Fin 2) :
    logicalBitSign (if a = 0 then b else if b = 0 then 1 else 0) =
      logicalBitSign a * logicalBitSign b := by
  fin_cases a <;> fin_cases b <;> norm_num [logicalBitSign]

/-- All nontarget coordinates survive the parity computation unchanged. -/
theorem cnotParityWord_else (t : Fin k) (L : List (Fin k)) (h : ∀ c ∈ L, c ≠ t)
    (x : QubitBasis k) {i : Fin k} (hi : i ≠ t) : cnotParityWord t L h x i = x i := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [cnotParityWord, Equiv.Perm.mul_apply, cnotWord_else _ _ _ _ hi]
    exact ih _

/-- The final Z eigenvalue at the target is the product of the input
signs of the controls and the input sign at the target. -/
theorem cnotParityWord_target_sign (t : Fin k) (L : List (Fin k)) (h : ∀ c ∈ L, c ≠ t)
    (x : QubitBasis k) :
    logicalBitSign (cnotParityWord t L h x t) =
      (L.map fun c => logicalBitSign (x c)).prod * logicalBitSign (x t) := by
  induction L with
  | nil => simp [cnotParityWord]
  | cons c L ih =>
    rw [cnotParityWord, Equiv.Perm.mul_apply, cnotWord_at_target, cnotBitSign,
      cnotParityWord_else _ _ _ _ (h c (List.mem_cons_self ..)), ih]
    simp [mul_assoc]

private theorem basisPermutation_conjugates_diagonal {β : Type*} [Fintype β] [DecidableEq β]
    (p : Equiv.Perm β) (f : β → ℂ) :
    CriticalDepth.BinaryPermutationUnitary.basisPermutation p.symm * diagonal f *
      CriticalDepth.BinaryPermutationUnitary.basisPermutation p = diagonal (f ∘ p) := by
  classical
  open CriticalDepth.BinaryPermutationUnitary in
  ext x y
  rw [Matrix.mul_assoc, basisPermutation_mul_apply, Equiv.symm_symm]
  rw [Matrix.diagonal_mul, basisPermutation_apply]
  by_cases h : x = y
  · subst y
    simp [Matrix.diagonal_apply_eq]
  · have hp : p x ≠ p y := fun he => h (p.injective he)
    simp [h, hp, Matrix.diagonal_apply_ne _ h]

private theorem basisPermutation_conjugates_rotation {β : Type*} [Fintype β] [DecidableEq β]
    (p : Equiv.Perm β) (f : β → ℂ) (t : ℝ) :
    CriticalDepth.BinaryPermutationUnitary.basisPermutation p.symm * rotation (diagonal f) t *
      CriticalDepth.BinaryPermutationUnitary.basisPermutation p = rotation (diagonal (f ∘ p)) t := by
  open CriticalDepth.BinaryPermutationUnitary in
  have h : basisPermutation p.symm * basisPermutation p = 1 :=
    (basisPermutation_conjTranspose p ▸ (basisPermutation_isUnitary p).1)
  rw [rotation, rotation, affine, affine]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    h, basisPermutation_conjugates_diagonal]

/-- An arbitrary tensor Z rotation with nonempty support is a CNOT
parity computation, one single-site Z rotation, and the inverse word. -/
theorem tensorZRotation_via_cnotParity (S : Finset (Fin k)) (t : Fin k) (ht : t ∈ S) (a : ℝ) :
    let L := (S.erase t).toList
    let h : ∀ i ∈ L, i ≠ t := fun _ hi =>
      (Finset.mem_erase.mp (Finset.mem_toList.mp hi)).1
    let p := cnotParityWord t L h
    CriticalDepth.BinaryPermutationUnitary.basisPermutation p.symm *
        rotation (pauliMatrix 0 (zSubset {t})) a *
        CriticalDepth.BinaryPermutationUnitary.basisPermutation p =
      rotation (pauliMatrix 0 (zSubset S)) a := by
  dsimp only
  rw [pauliMatrix_zSubset, pauliMatrix_zSubset]
  simp only [Finset.prod_singleton]
  rw [basisPermutation_conjugates_rotation]
  congr 2
  funext x
  change logicalBitSign (cnotParityWord t (S.erase t).toList _ x t) = _
  rw [cnotParityWord_target_sign, Finset.prod_map_toList, mul_comm]
  exact (mul_comm _ _).trans (Finset.prod_erase_mul _ _ ht)

#print axioms cnotParityWord_target_sign
#print axioms tensorZRotation_via_cnotParity

end

end CriticalDepth.Manuscript20261114
