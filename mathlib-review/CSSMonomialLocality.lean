import ShorRowAction
import FaultCircuitSupport
import CSSPermutationRigidity
import CSSComputationalMonomial

/-!
# Locality of monomial physical unitaries

A monomial matrix is represented in the binary coordinates of the actual
physical computational basis. Its matrix columns have unit-modulus phases.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.FaultCircuitSupport CriticalDepth.BinaryPermutationUnitary
open Matrix

variable {n : ℕ}

def binaryMonomial (U : Operator (QubitBasis n)) (f : Equiv.Perm (BinaryWord (Fin n)))
    (u : BinaryWord (Fin n) → ℂˣ) : Prop :=
  ∀ x y, U ((binaryWordEquiv n).symm x) ((binaryWordEquiv n).symm y) =
    if x = f y then (u y : ℂ) else 0

private theorem supported_entry_zero {S : Finset (Fin n)} {O : Operator (QubitBasis n)}
    (hO : SupportedOn O S) (x y : QubitBasis n) (i : Fin n) (hi : i ∉ S) (hne : x i ≠ y i) :
    O x y = 0 := by
  obtain ⟨A, rfl⟩ := hO
  unfold localEmbed
  have h : ¬ ∀ j, j ∉ S → x j = y j := fun he => hne (he i hi)
  exact if_neg h

private theorem supported_diag_depends {S : Finset (Fin n)} {O : Operator (QubitBasis n)}
    (hO : SupportedOn O S) :
    DependsOn S (fun x : BinaryWord (Fin n) => O ((binaryWordEquiv n).symm x)
      ((binaryWordEquiv n).symm x)) := by
  obtain ⟨A, rfl⟩ := hO
  intro x y hxy
  unfold localEmbed
  have ht : (fun i : S => (binaryWordEquiv n).symm x i.val) =
      (fun i : S => (binaryWordEquiv n).symm y i.val) := by
    funext i
    exact congrArg qubitBitEquiv.symm (hxy i.val i.property)
  simp only [imp_true_iff, implies_true, ite_true, ht]

private theorem mul_monomial_apply
    (U : Operator (QubitBasis n)) (f : Equiv.Perm (BinaryWord (Fin n)))
    (u : BinaryWord (Fin n) → ℂˣ) (h : binaryMonomial U f u)
    (A : Operator (QubitBasis n)) (x y : BinaryWord (Fin n)) :
    (A * U) ((binaryWordEquiv n).symm x) ((binaryWordEquiv n).symm y) =
      A ((binaryWordEquiv n).symm x) ((binaryWordEquiv n).symm (f y)) * (u y : ℂ) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single ((binaryWordEquiv n).symm (f y))]
  · rw [h, if_pos rfl]
  · intro j _ hj
    let z := (binaryWordEquiv n) j
    have he : (binaryWordEquiv n).symm z = j := Equiv.symm_apply_apply _ _
    have hn : z ≠ f y := fun hh => hj (he.symm.trans (congrArg (binaryWordEquiv n).symm hh))
    rw [← he, h, if_neg hn, mul_zero]
  · simp

private theorem monomial_mul_apply
    (U : Operator (QubitBasis n)) (f : Equiv.Perm (BinaryWord (Fin n)))
    (u : BinaryWord (Fin n) → ℂˣ) (h : binaryMonomial U f u)
    (A : Operator (QubitBasis n)) (x y : BinaryWord (Fin n)) :
    (U * A) ((binaryWordEquiv n).symm (f x)) ((binaryWordEquiv n).symm y) =
      (u x : ℂ) * A ((binaryWordEquiv n).symm x) ((binaryWordEquiv n).symm y) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single ((binaryWordEquiv n).symm x)]
  · rw [h, if_pos rfl]
  · intro j _ hj
    let z := (binaryWordEquiv n) j
    have he : (binaryWordEquiv n).symm z = j := Equiv.symm_apply_apply _ _
    have hn : f x ≠ f z := fun hh =>
      hj (he.symm.trans (congrArg (binaryWordEquiv n).symm (f.injective hh).symm))
    rw [← he, h, if_neg hn, zero_mul]
  · simp

theorem monomial_conjugate_entry
    (U : Operator (QubitBasis n)) (hu : IsUnitary U)
    (f : Equiv.Perm (BinaryWord (Fin n))) (u : BinaryWord (Fin n) → ℂˣ)
    (h : binaryMonomial U f u) (A : Operator (QubitBasis n)) (x y : BinaryWord (Fin n)) :
    propagate U A ((binaryWordEquiv n).symm (f x)) ((binaryWordEquiv n).symm (f y)) *
      (u y : ℂ) = (u x : ℂ) * A ((binaryWordEquiv n).symm x) ((binaryWordEquiv n).symm y) := by
  have he : propagate U A * U = U * A := by
    unfold propagate
    have huL : U.conjTranspose * U = 1 := hu.1
    rw [Matrix.mul_assoc (U * A), huL, Matrix.mul_one]
  have he' := congrArg
    (fun M : Operator (QubitBasis n) => M ((binaryWordEquiv n).symm (f x)) ((binaryWordEquiv n).symm y)) he
  rwa [mul_monomial_apply U f u h, monomial_mul_apply U f u h] at he'

theorem monomial_adjoint_conjugate_diagonal_entry
    (U : Operator (QubitBasis n)) (hu : IsUnitary U)
    (f : Equiv.Perm (BinaryWord (Fin n))) (u : BinaryWord (Fin n) → ℂˣ)
    (h : binaryMonomial U f u) (A : Operator (QubitBasis n)) (x : BinaryWord (Fin n)) :
    propagate U.conjTranspose A ((binaryWordEquiv n).symm x) ((binaryWordEquiv n).symm x) =
      A ((binaryWordEquiv n).symm (f x)) ((binaryWordEquiv n).symm (f x)) := by
  let B := propagate U.conjTranspose A
  have hB : propagate U B = A := by
    change U * (U.conjTranspose * A * U.conjTranspose.conjTranspose) * U.conjTranspose = A
    have huR : U * U.conjTranspose = 1 := hu.2
    rw [Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc U, ← Matrix.mul_assoc U,
      huR, Matrix.one_mul, Matrix.mul_assoc, huR, Matrix.mul_one]
  have he := monomial_conjugate_entry U hu f u h B x x
  rw [hB, mul_comm (u x : ℂ)] at he
  exact (mul_right_cancel₀ (Units.ne_zero (u x)) he).symm

private theorem siteZSign_inv_bit (i : Fin n) (x : BinaryWord (Fin n)) :
    CriticalDepth.CSSMonomial.siteZSign i ((binaryWordEquiv n).symm x) =
      if x i = 0 then 1 else -1 := by
  change (if qubitBitEquiv.symm (x i) = 0 then (1 : ℂ) else -1) = _
  have eq : ∀ a : ZMod 2, qubitBitEquiv.symm a = 0 ↔ a = 0 := by decide
  simp only [eq]

theorem monomial_permutation_dependsOn {U : Operator (QubitBasis n)}
    (hu : IsUnitary U) {f : Equiv.Perm (BinaryWord (Fin n))}
    {u : BinaryWord (Fin n) → ℂˣ} (h : binaryMonomial U f u) (i : Fin n)
    (S : Finset (Fin n))
    (hS : SupportedOn (propagate U.conjTranspose (pauliMatrix 0 (singleSitePauli i .Z))) S) :
    DependsOn S (fun x => f x i) := by
  intro x y hxy
  have he : propagate U.conjTranspose (pauliMatrix 0 (singleSitePauli i .Z))
      ((binaryWordEquiv n).symm x) ((binaryWordEquiv n).symm x) =
    propagate U.conjTranspose (pauliMatrix 0 (singleSitePauli i .Z))
      ((binaryWordEquiv n).symm y) ((binaryWordEquiv n).symm y) := supported_diag_depends hS x y hxy
  rw [monomial_adjoint_conjugate_diagonal_entry U hu f u h,
    monomial_adjoint_conjugate_diagonal_entry U hu f u h,
    CriticalDepth.CSSMonomial.singleSitePauli_z_eq_diagonal,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, siteZSign_inv_bit, siteZSign_inv_bit] at he
  have inject : Function.Injective (fun a : ZMod 2 => if a = 0 then (1 : ℂ) else -1) := by
    intro a b
    change (if a = 0 then (1 : ℂ) else -1) = (if b = 0 then 1 else -1) → a = b
    have hb (k : ZMod 2) : k = 0 ∨ k = 1 := (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) k
    rcases hb a with e | e <;> rcases hb b with e' | e' <;> norm_num [e, e']
  exact inject he

theorem pauli_singleX_binary_entry (i : Fin n) (x y : BinaryWord (Fin n)) :
    pauliMatrix 0 (singleSitePauli i .X) ((binaryWordEquiv n).symm x)
      ((binaryWordEquiv n).symm y) = if x = y + Pi.single i 1 then 1 else 0 := by
  classical
  let e := binaryWordEquiv n
  rw [CriticalDepth.ReviewV2.PauliRowAction.pauliMatrix_row]
  have hcoeff : CriticalDepth.ReviewV2.PauliRowAction.rowCoefficient (singleSitePauli i .X)
      (e.symm x) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    by_cases hj : j = i <;> simp [singleSitePauli, hj,
      CriticalDepth.ReviewV2.PauliRowAction.singleCoefficient]
  have hflip : e (CriticalDepth.ReviewV2.PauliRowAction.flipWord (singleSitePauli i .X) (e.symm x)) =
      x + Pi.single i 1 := by
    funext j
    change qubitBitEquiv (CriticalDepth.ReviewV2.PauliRowAction.singleFlip
      (singleSitePauli i .X j) (qubitBitEquiv.symm (x j))) = _
    by_cases hj : j = i
    · subst j
      simp only [singleSitePauli, if_pos rfl, Pi.add_apply, Pi.single_eq_same]
      exact (by decide : ∀ a : ZMod 2,
        qubitBitEquiv (1 - qubitBitEquiv.symm a) = a + 1) _
    · simp [singleSitePauli, hj, CriticalDepth.ReviewV2.PauliRowAction.singleFlip,
        Pi.single_eq_of_ne hj]
  have he : e.symm y = CriticalDepth.ReviewV2.PauliRowAction.flipWord (singleSitePauli i .X)
      (e.symm x) ↔ x = y + Pi.single i 1 := by
    rw [← e.injective.eq_iff, Equiv.apply_symm_apply, hflip]
    have ht : (Pi.single i 1 : BinaryWord (Fin n)) + Pi.single i 1 = 0 := by
      funext j
      exact (by decide : ∀ a : ZMod 2, a + a = 0) _
    constructor <;> intro hx
    · rw [hx, add_assoc, ht, add_zero]
    · rw [hx, add_assoc, ht, add_zero]
  rw [hcoeff]
  by_cases hz : x = y + Pi.single i 1
  · rw [ite_eq_left hz, ite_eq_left (he.mpr hz)]
  · rw [ite_eq_right hz, ite_eq_right (fun h => hz (he.mp h))]

theorem monomial_bitDifference_zero_of_outside {U : Operator (QubitBasis n)}
    (hu : IsUnitary U) {f : Equiv.Perm (BinaryWord (Fin n))}
    {u : BinaryWord (Fin n) → ℂˣ} (h : binaryMonomial U f u) (j : Fin n)
    (S : Finset (Fin n))
    (hS : SupportedOn (propagate U (pauliMatrix 0 (singleSitePauli j .X))) S) :
    ∀ x i, i ∉ S → bitDifference f j x i = 0 := by
  intro x i hi
  let y := x + Pi.single j 1
  have hentry := monomial_conjugate_entry U hu f u h (pauliMatrix 0 (singleSitePauli j .X)) y x
  rw [pauli_singleX_binary_entry, if_pos rfl, mul_one] at hentry
  have nz : propagate U (pauliMatrix 0 (singleSitePauli j .X))
      ((binaryWordEquiv n).symm (f y)) ((binaryWordEquiv n).symm (f x)) ≠ 0 :=
    fun hzero => Units.ne_zero (u y) (by simpa [hzero] using hentry.symm)
  have hbit : f y i = f x i := by
    by_contra hn
    exact nz (supported_entry_zero hS _ _ i hi (qubitBitEquiv.symm.injective.ne hn))
  change f y i + f x i = 0
  rw [hbit]
  exact (by decide : ∀ a : ZMod 2, a + a = 0) _

#print axioms monomial_permutation_dependsOn
#print axioms monomial_bitDifference_zero_of_outside
#print axioms monomial_conjugate_entry
#print axioms monomial_adjoint_conjugate_diagonal_entry

end CriticalDepth.Manuscript20261114.CSSCheckSpaces