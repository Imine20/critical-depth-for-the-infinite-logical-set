import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace CriticalDepth.Manuscript20261114

/-- For a normalized syndrome branch, its probability-weighted success
is bounded by the largest mass of a logical Pauli class in that branch. -/
theorem pauliClassSuccess_le {ι : Type*} [Fintype ι]
    (mass fidelity : ι → ℝ) (upper : ℝ)
    (hf : ∀ i, 0 ≤ fidelity i) (hsum : ∑ i, fidelity i = 1)
    (hupper : ∀ i, mass i ≤ upper) :
    ∑ i, mass i * fidelity i ≤ upper := by
  classical
  calc
    ∑ i, mass i * fidelity i ≤ ∑ i, upper * fidelity i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hupper i) (hf i)
    _ = upper := by rw [← Finset.mul_sum, hsum, mul_one]

/-- The upper bound is reached when the recovery assigns its entire
fidelity to a maximum-mass class. -/
theorem pauliClassSuccess_at_choice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mass : ι → ℝ) (selected : ι) :
    ∑ i, mass i * (if i = selected then (1 : ℝ) else 0) = mass selected := by
  simp [mul_ite]

/-- The classical optimization over syndrome-conditioned fidelity vectors.
The CPTP representation supplies both the constraints and the extremizers. -/
theorem syndromeSuccess_optimum {S L : Type*} [Fintype S] [Fintype L] [DecidableEq L]
    (mass : S → L → ℝ) (selected : S → L)
    (hselected : ∀ s l, mass s l ≤ mass s (selected s)) :
    (∀ fidelity : S → L → ℝ,
      (∀ s l, 0 ≤ fidelity s l) → (∀ s, ∑ l, fidelity s l = 1) →
      (∑ s, ∑ l, mass s l * fidelity s l) ≤ ∑ s, mass s (selected s)) ∧
      (∑ s, ∑ l, mass s l * (if l = selected s then (1 : ℝ) else 0)) =
        ∑ s, mass s (selected s) := by
  constructor
  · intro fidelity hnonneg hnorm
    exact Finset.sum_le_sum fun s _ =>
      pauliClassSuccess_le (mass s) (fidelity s) (mass s (selected s))
        (hnonneg s) (hnorm s) (hselected s)
  · exact Finset.sum_congr rfl fun s _ => pauliClassSuccess_at_choice (mass s) (selected s)

example (p : ℝ) (hp : p ≤ 1 - p) :
    (∑ i : Fin 2, (if i = 0 then 1 - p else p) * (if i = 0 then (1 : ℝ) else 0)) =
      1 - p := by
  simpa using pauliClassSuccess_at_choice
    (fun i : Fin 2 => if i = 0 then 1 - p else p) (0 : Fin 2)

#print axioms pauliClassSuccess_le
#print axioms pauliClassSuccess_at_choice
#print axioms syndromeSuccess_optimum

end CriticalDepth.Manuscript20261114
