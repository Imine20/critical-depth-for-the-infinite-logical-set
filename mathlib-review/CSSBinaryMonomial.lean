import CSSMonomialPhaseLocality

/-!
Converting a matrix-entry monomial form into a unit-valued phase
function in binary computational coordinates.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation

variable {n : ℕ}

theorem exists_binaryMonomial_of_basis_form (U : Operator (QubitBasis n))
    (f : Equiv.Perm (QubitBasis n)) (a : QubitBasis n → ℂ)
    (hu : ∀ y, star (a y) * a y = 1)
    (hU : ∀ x y, U x y = if x = f y then a y else 0) :
    ∃ (f' : Equiv.Perm (BinaryWord (Fin n))) (u' : BinaryWord (Fin n) → ℂˣ),
      binaryMonomial U f' u' ∧ ∀ x, star ((u' x : ℂ)) * (u' x : ℂ) = 1 := by
  classical
  let e := binaryWordEquiv n
  let f' := (e.symm.trans f).trans e
  let u' (x : BinaryWord (Fin n)) : ℂˣ :=
    ⟨a (e.symm x), star (a (e.symm x)), by rw [mul_comm, hu], hu _⟩
  refine ⟨f', u', ?_, fun x => hu _⟩
  intro x y
  rw [hU]
  have hf : e.symm x = f (e.symm y) ↔ x = f' y := by
    constructor
    · intro h
      change x = e (f (e.symm y))
      rw [← h, e.apply_symm_apply]
    · intro h
      change x = e (f (e.symm y)) at h
      rw [h, e.symm_apply_apply]
  by_cases h : x = f' y
  · rw [ite_eq_left h, ite_eq_left (hf.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (hf.mp hh))]

#print axioms exists_binaryMonomial_of_basis_form

end CriticalDepth.Manuscript20261114.CSSCheckSpaces