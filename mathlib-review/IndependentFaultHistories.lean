import FaultProbability
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
Finite product noise at the actual gate locations. The type of nonidentity
labels can depend on the location, so labels on different supports need
not use the same alphabet.
-/

namespace CriticalDepth.IndependentFaultHistories

open scoped BigOperators
open CriticalDepth.FaultProbability

noncomputable section

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

abbrev History (Label : Loc → Type*) := ∀ i, Option (Label i)

/-- Nonempty native locations have a positive distribution on the
nonidentity fault labels. Clean behavior is the extra option. -/
structure Law (Label : Loc → Type*) [∀ i, Fintype (Label i)] where
  weight : ∀ i, Label i → ℝ
  positive : ∀ i a, 0 < weight i a
  normalized : ∀ i, ∑ a, weight i a = 1

def faults (x : History Label) : Finset Loc :=
  Finset.univ.filter fun i => x i ≠ none

def localMass (μ : Law Label) (p : ℝ) (i : Loc) : Option (Label i) → ℝ
  | none => 1 - p
  | some a => μ.weight i a * p

def mass (μ : Law Label) (p : ℝ) (x : History Label) : ℝ :=
  ∏ i, localMass μ p i (x i)

theorem localMass_nonneg (μ : Law Label) {p : ℝ}
    (hp : 0 ≤ p) (hp₁ : p ≤ 1) (i : Loc) (a : Option (Label i)) :
    0 ≤ localMass μ p i a := by
  cases a with
  | none => exact sub_nonneg.mpr hp₁
  | some a => exact mul_nonneg (μ.positive i a).le hp

theorem mass_nonneg (μ : Law Label) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : History Label) : 0 ≤ mass μ p x :=
  Finset.prod_nonneg fun i _ => localMass_nonneg μ hp hp₁ i (x i)

private theorem sum_site (μ : Law Label) (p : ℝ) (i : Loc) :
    ∑ a, localMass μ p i a = 1 := by
  rw [Fintype.sum_option]
  simp only [localMass, ← Finset.sum_mul, μ.normalized, one_mul]
  ring

private theorem sum_faulty_site (μ : Law Label) (p : ℝ) (i : Loc) :
    (∑ a : Option (Label i), if a ≠ none then localMass μ p i a else 0) = p := by
  rw [Fintype.sum_option]
  simp [localMass, ← Finset.sum_mul, μ.normalized]

theorem sum_mass (μ : Law Label) (p : ℝ) : ∑ x, mass μ p x = 1 := by
  rw [show (∑ x, mass μ p x) = ∏ i, ∑ a, localMass μ p i a from
    (Fintype.prod_sum (localMass μ p)).symm]
  simp only [sum_site, Finset.prod_const_one]

/-- Every specified set of faulty locations has joint probability
exactly the corresponding power of the per-location failure rate. -/
theorem jointMass (μ : Law Label) (p : ℝ) (s : Finset Loc) :
    ∑ x ∈ Finset.univ.filter (fun x : History Label => s ⊆ faults x), mass μ p x =
      p ^ s.card := by
  classical
  let f (i : Loc) (a : Option (Label i)) :=
    if i ∈ s → a ≠ none then localMass μ p i a else 0
  have hf (x : History Label) :
      (∏ i, f i (x i)) = if s ⊆ faults x then mass μ p x else 0 := by
    have h : (∀ i, i ∈ s → x i ≠ none) ↔ s ⊆ faults x := by
      simp [Finset.subset_iff, faults]
    simpa only [f, mass, h] using
      (Fintype.prod_ite_zero (p := fun i => i ∈ s → x i ≠ none)
        (f := fun i => localMass μ p i (x i)))
  rw [Finset.sum_filter]
  simp_rw [← hf]
  rw [← Fintype.prod_sum]
  have hsum (i : Loc) : (∑ a, f i a) = if i ∈ s then p else 1 := by
    by_cases hi : i ∈ s
    · simpa only [f, hi, true_implies, ite_true] using sum_faulty_site μ p i
    · simpa only [f, hi, false_implies, ite_true, ite_false] using sum_site μ p i
  simp_rw [hsum]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  simp

theorem tail (μ : Law Label) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (m : ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : History Label => m ≤ (faults x).card), mass μ p x ≤
      ((Fintype.card Loc).choose m : ℝ) * p ^ m := by
  classical
  simpa only [Finset.card_univ] using
    (localStochasticTail Finset.univ (Finset.univ : Finset Loc) faults (mass μ p) m p
      (fun x _ => mass_nonneg μ hp hp₁ x) (fun x _ => Finset.subset_univ (faults x))
      (fun s _ => le_of_eq (jointMass μ p s)))

def conditionalWeight (μ : Law Label) (x : History Label) : ℝ :=
  ∏ i, (x i).elim 1 (μ.weight i)

theorem conditionalWeight_pos (μ : Law Label) (x : History Label) :
    0 < conditionalWeight μ x := by
  apply Finset.prod_pos
  intro i _
  cases h : x i with
  | none => simp [h]
  | some a => simpa [h] using μ.positive i a

theorem mass_eq_historyMass (μ : Law Label) (p : ℝ) (x : History Label) :
    mass μ p x = historyMass p (conditionalWeight μ x) (faults x).card
      (Fintype.card Loc - (faults x).card) := by
  classical
  have h (i : Loc) : localMass μ p i (x i) =
      (x i).elim 1 (μ.weight i) * (if i ∈ faults x then p else 1 - p) := by
    cases hx : x i <;> simp [localMass, faults, hx]
  simp only [mass, h, Finset.prod_mul_distrib, historyMass, conditionalWeight]
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
    Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ (faults x)), Finset.card_univ]

#print axioms jointMass
#print axioms tail
#print axioms mass_eq_historyMass

end
end CriticalDepth.IndependentFaultHistories
