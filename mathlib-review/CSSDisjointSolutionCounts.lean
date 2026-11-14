import CSSFiniteColumns

/-!
Counterexample counting for random binary generators.

An unrestricted generator matrix can be sampled as a tuple of rows or a
tuple of columns. The bounds below count independent row equations
directly, using disjoint variable sets.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

section Coordinates

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- A system of equations, each of which can be solved for one distinct
coordinate without consulting the other selected coordinates, has at most
one solution for each assignment on the complement. -/
theorem card_solutions_le_complement (pivots : Finset ι)
    (S : Finset (ι → V))
    (h : ∀ x ∈ S, ∀ y ∈ S, (∀ i ∉ pivots, x i = y i) → x = y) :
    S.card ≤ Fintype.card V ^ (Fintype.card ι - pivots.card) := by
  classical
  let f : S → ((pivotsᶜ : Finset ι) → V) := fun x i => x.val i.val
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply h _ x.property _ y.property
    intro i hi
    exact congrFun he ⟨i, by simpa using hi⟩
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_fun, Finset.card_compl] using hc

/-- Pairwise disjoint variable sets permit all selected pivot variables
to be omitted from the count of independent equations. -/
theorem card_disjoint_solutions_le {κ : Type*} [DecidableEq κ]
    (rows : Finset κ) (vars : κ → Finset ι) (pivot : κ → ι)
    (hp : ∀ i ∈ rows, pivot i ∈ vars i)
    (hd : (rows : Set κ).PairwiseDisjoint vars)
    (S : Finset (ι → V))
    (hsolve : ∀ i ∈ rows, ∀ x ∈ S, ∀ y ∈ S,
      (∀ j ∈ vars i, j ≠ pivot i → x j = y j) → x (pivot i) = y (pivot i)) :
    S.card ≤ Fintype.card V ^ (Fintype.card ι - rows.card) := by
  classical
  have hpinj : Set.InjOn pivot (rows : Set κ) := by
    intro i hi j hj hij
    by_contra hne
    exact Finset.disjoint_left.mp (hd hi hj hne) (hp i hi) (hij.symm ▸ hp j hj)
  let p := rows.image pivot
  have hc : p.card = rows.card := Finset.card_image_of_injOn hpinj
  rw [← hc]
  apply card_solutions_le_complement p S
  intro x hx y hy hn
  funext j
  by_cases hj : j ∈ p
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    apply hsolve i hi x hx y hy
    intro k hvars hk
    apply hn k
    intro hkp
    obtain ⟨r, hr, hrk⟩ := Finset.mem_image.mp hkp
    have hri : r ≠ i := fun he => hk (he ▸ hrk).symm
    exact Finset.disjoint_left.mp (hd hr hi hri) (hrk ▸ hp r hr) hvars
  · exact hn j hj

end Coordinates

#print axioms card_solutions_le_complement
#print axioms card_disjoint_solutions_le

end CriticalDepth.Manuscript20261114.CSSCheckSpaces