import ShorNativeSitePermutation

/-!
# Exact wire swaps from connected edge swaps
-/

namespace CriticalDepth.Manuscript20261114

open Relation CriticalDepth.FaultShorSaturation CriticalDepth.BinaryPermutationUnitary
open CriticalDepth.Manuscript

variable {ι α : Type*} [DecidableEq ι]

/-- Evaluate an ordered list of sites as a product of transpositions. -/
def edgeSwapWord (L : List (ι × ι)) : Equiv.Perm ι :=
  (L.map fun e => Equiv.swap e.1 e.2).prod

@[simp] theorem edgeSwapWord_nil : edgeSwapWord ([] : List (ι × ι)) = 1 := rfl

theorem edgeSwapWord_append (L M : List (ι × ι)) :
    edgeSwapWord (L ++ M) = edgeSwapWord L * edgeSwapWord M := by
  rw [edgeSwapWord, List.map_append, List.prod_append]
  rfl

/-- A path yields an exact finite edge-swap word for its endpoint
transposition. Repeated vertices and equality of the endpoints are allowed. -/
theorem exists_edgeSwapWord_of_path {E : ι → ι → Prop} {i j : ι}
    (h : ReflTransGen E i j) :
    ∃ L : List (ι × ι), (∀ e ∈ L, E e.1 e.2) ∧ edgeSwapWord L = Equiv.swap i j := by
  induction h with
  | refl => exact ⟨[], by simp, by rw [edgeSwapWord_nil, Equiv.swap_self]; rfl⟩
  | @tail j l _ he ih =>
    by_cases hil : i = l
    · subst l
      exact ⟨[], by simp, by rw [edgeSwapWord_nil, Equiv.swap_self]; rfl⟩
    by_cases hij : i = j
    · subst j
      exact ⟨[(i,l)], by simpa, by simp [edgeSwapWord]⟩
    by_cases hjl : j = l
    · subst l
      exact ih
    obtain ⟨L, hL, hEq⟩ := ih
    refine ⟨[(j,l)] ++ L ++ [(j,l)], ?_, ?_⟩
    · intro e he'
      simp only [List.mem_append, List.mem_singleton] at he'
      rcases he' with (rfl | hL') | rfl
      · exact he
      · exact hL _ hL'
      · exact he
    · rw [edgeSwapWord_append, edgeSwapWord_append, hEq]
      simp only [edgeSwapWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [Equiv.swap_mul_swap_mul_swap hij hil, Equiv.swap_comm l i]

/-- Conjugation by a wire permutation sends a swap to the corresponding
swap of the permuted sites. -/
theorem wireSwap_conjugate (p : Equiv.Perm ι) (i j : ι) :
    p * Equiv.swap i j * p⁻¹ = Equiv.swap (p i) (p j) := by
  simpa only [Equiv.Perm.mul_def, Equiv.Perm.inv_def, Equiv.trans_assoc] using
    (Equiv.symm_trans_swap_trans i j p)

theorem permuteSites_mul (p q : Equiv.Perm ι) :
    (permuteSites (α := α) (p * q)) =
      permuteSites p * permuteSites q := by
  ext x i
  rfl

/-- Physical computational-basis permutation matrices preserve exactly
the order and product of the wire-permutation word. -/
theorem edgeSwapWord_physical {k : ℕ} (L : List (Fin k × Fin k)) :
    (L.map fun e => basisPermutation (permuteSites (α := Fin 2) (Equiv.swap e.1 e.2))).prod =
      basisPermutation (permuteSites (α := Fin 2) (edgeSwapWord L)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, edgeSwapWord_nil]
    ext x y
    have h : permuteSites (α := Fin 2) (1 : Equiv.Perm (Fin k)) y = y := rfl
    rw [basisPermutation_apply, h, Matrix.one_apply]
  | cons e L ih =>
    simp only [List.map_cons, List.prod_cons, edgeSwapWord] at ih ⊢
    rw [ih, permuteSites_mul, basisPermutation_mul]
    rfl

#print axioms exists_edgeSwapWord_of_path
#print axioms wireSwap_conjugate
#print axioms edgeSwapWord_physical

end CriticalDepth.Manuscript20261114
