import ExactGraphEdgeOperator
import ExactPauliParityCircuit

/-!
# Routing a CNOT by wire permutations
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary
open CriticalDepth.FaultShorSaturation

noncomputable section

variable {k : ℕ}

private theorem permuteSites_inv (p : Equiv.Perm (Fin k)) :
    (permuteSites (α := Fin 2) p)⁻¹ = permuteSites p⁻¹ := rfl

/-- Relabeling the register before and after a CNOT moves its control and
target to the images of those sites, with the relabeling undone. -/
theorem cnotWord_conjugate (p : Equiv.Perm (Fin k)) (c t : Fin k) (hct : c ≠ t) :
    permuteSites p * cnotWord c t hct * (permuteSites (α := Fin 2) p)⁻¹ =
      cnotWord (p c) (p t) (p.injective.ne hct) := by
  apply Equiv.ext
  intro x
  funext i
  simp only [Equiv.Perm.mul_apply, permuteSites_inv]
  change cnotWord c t hct (fun u => x (p u)) (p.symm i) =
    cnotWord (p c) (p t) (p.injective.ne hct) x i
  by_cases h : i = p t
  · subst i
    rw [p.symm_apply_apply, cnotWord_at_target, cnotWord_at_target]
  · have h' : p.symm i ≠ t := fun he => h ((p.apply_symm_apply i).symm.trans (congrArg p he))
    rw [cnotWord_else _ _ _ _ h', cnotWord_else _ _ _ _ h, p.apply_symm_apply]

/-- The matrix of the wire-routed CNOT has the same exact conjugation. -/
theorem basisPermutation_cnotWord_conjugate (p : Equiv.Perm (Fin k))
    (c t : Fin k) (hct : c ≠ t) :
    basisPermutation (permuteSites p) * basisPermutation (cnotWord c t hct) *
        basisPermutation ((permuteSites (α := Fin 2) p)⁻¹) =
      basisPermutation (cnotWord (p c) (p t) (p.injective.ne hct)) := by
  rw [basisPermutation_mul, basisPermutation_mul]
  change basisPermutation (permuteSites p * cnotWord c t hct * (permuteSites p)⁻¹) = _
  rw [cnotWord_conjugate]

/-- The edge-local CNOT matrix from the exact CZ identity acts by the
computational CNOT used for parity calculation. -/
theorem edgeOperator_cnotWord (c t : Fin k) (hct : c ≠ t) :
    edgeOperator c t hct pairCNOT = basisPermutation (cnotWord c t hct) := by
  classical
  ext x y
  rw [edgeOperator_apply, basisPermutation_apply]
  let b : Fin 2 := if y c = 0 then y t else if y t = 0 then 1 else 0
  have ht : cnotWord c t hct y t = b := cnotWord_at_target c t hct y
  have hf : x = cnotWord c t hct y ↔
      (∀ s, s ≠ c → s ≠ t → x s = y s) ∧ x c = y c ∧ x t = b := by
    constructor
    · intro h
      exact ⟨fun s _ hst => (congrFun h s).trans (cnotWord_else _ _ _ _ hst),
        (congrFun h c).trans (cnotWord_else _ _ _ _ hct), (congrFun h t).trans ht⟩
    · rintro ⟨ho,hc,hxt⟩
      funext s
      by_cases hs : s = c
      · subst s
        exact hc.trans (cnotWord_else _ _ _ _ hct).symm
      by_cases hst : s = t
      · subst s
        exact hxt.trans ht.symm
      exact (ho s hs hst).trans (cnotWord_else _ _ _ _ hst).symm
  simp only [hf]
  by_cases ho : ∀ s, s ≠ c → s ≠ t → x s = y s
  · rw [ite_eq_left ho]
    have hrest : ((∀ s, s ≠ c → s ≠ t → x s = y s) ∧ x c = y c ∧ x t = b) ↔
        (x c = y c ∧ x t = b) := ⟨fun hx => hx.2, fun hx => ⟨ho,hx⟩⟩
    simp only [hrest, pairCNOT]
    have hBit (a u v : Fin 2) :
        (if a = 0 then (1 : Operator (Fin 2)) else SinglePauli.X.matrix) u v =
          if u = (if a = 0 then v else if v = 0 then 1 else 0) then 1 else 0 := by
      fin_cases a <;> fin_cases u <;> fin_cases v <;>
        simp [SinglePauli.matrix, Matrix.one_apply]
    rw [hBit]
    by_cases hc : x c = y c <;> simp [hc, b]
  · rw [ite_eq_right ho]
    simp only [ho, false_and, ite_false]

#print axioms cnotWord_conjugate
#print axioms basisPermutation_cnotWord_conjugate
#print axioms edgeOperator_cnotWord

end

end CriticalDepth.Manuscript20261114
