import UnitaryAdjointSpan
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Finite tangent families from dense unitary subgroups

The span of the conjugates under a dense subgroup agrees with the span of
the whole unitary orbit. Then finite dimensionality lets us choose finitely
many subgroup elements whose conjugates, together with the scalar phase
velocity, span the same space.
-/

namespace CriticalDepth.UnitaryAdjointSpan

open Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem continuous_conj_fixed (X : Mat ι) :
    Continuous (fun U : Matrix.unitaryGroup ι ℂ => conj U X) := by
  rw [show (fun U : Matrix.unitaryGroup ι ℂ => conj U X) =
    (fun U : Matrix.unitaryGroup ι ℂ => (U : Mat ι) * X * star (U : Mat ι)) from rfl]
  exact (continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.star

/-- The phase together with a dense unitary orbit spans the same submodule
as the phase together with the entire unitary orbit. -/
theorem dense_conjugatesAndPhaseSpan_eq (X : Mat ι)
    {s : Set (Matrix.unitaryGroup ι ℂ)} (hs : Dense s) :
    Submodule.span ℝ (insert (Complex.I • (1 : Mat ι))
      ((fun U : Matrix.unitaryGroup ι ℂ => conj U X) '' s)) =
      conjugatesAndPhaseSpan X := by
  let f := fun U : Matrix.unitaryGroup ι ℂ => conj U X
  let E := Submodule.span ℝ (insert (Complex.I • (1 : Mat ι)) (f '' s))
  change E = conjugatesAndPhaseSpan X
  apply le_antisymm
  · apply Submodule.span_mono
    exact Set.insert_subset_insert (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with hscalar | hgen
    · exact Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl hscalar))
    · obtain ⟨U, rfl⟩ := hgen
      have hsubset : s ⊆ f ⁻¹' (E : Set (Mat ι)) := by
        intro V hV
        exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨V, hV, rfl⟩)
      have hclosed : IsClosed (f ⁻¹' (E : Set (Mat ι))) :=
        E.closed_of_finiteDimensional.preimage (continuous_conj_fixed X)
      have hle := closure_minimal hsubset hclosed
      rw [hs.closure_eq] at hle
      exact hle (Set.mem_univ U)

/-- Extract a finite family of unitary representatives from a dense subgroup.
The phase direction can be added as one further curve independently. -/
theorem exists_fin_conjugates_spanning_skewAdjoint (X : Mat ι)
    (hX : star X = -X) (hnonscalar : ¬ ∃ c : ℂ, X = c • (1 : Mat ι))
    (G : Subgroup (Matrix.unitaryGroup ι ℂ)) (hG : Dense (G : Set (Matrix.unitaryGroup ι ℂ))) :
    ∃ (n : ℕ) (U : Fin n → G),
      Submodule.span ℝ (insert (Complex.I • (1 : Mat ι))
        (Set.range fun i => conj (U i : Matrix.unitaryGroup ι ℂ) X)) =
          skewAdjoint.submodule ℝ (Mat ι) := by
  classical
  let K := skewAdjoint.submodule ℝ (Mat ι)
  let f := fun U : Matrix.unitaryGroup ι ℂ => conj U X
  let S := insert (Complex.I • (1 : Mat ι)) (f '' (G : Set _))
  have hS : Submodule.span ℝ S = K :=
    (dense_conjugatesAndPhaseSpan_eq X hG).trans
      (conjugatesAndPhaseSpan_eq_skewAdjoint X hX hnonscalar)
  have hfinite : K.FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨generators, hgenerators⟩ := hfinite
  have hcontains : (generators : Set (Mat ι)) ⊆ Submodule.span ℝ S := by
    rw [hS, ← hgenerators]
    exact Submodule.subset_span
  obtain ⟨witnesses, hwitnesses, hspan⟩ :=
    Submodule.subset_span_finite_of_subset_span hcontains
  let orbitWitnesses := witnesses.filter (fun A => A ≠ Complex.I • (1 : Mat ι))
  have hrep : ∀ A : orbitWitnesses, ∃ U : G, f U = (A : Mat ι) := by
    intro A
    obtain ⟨hm, hne⟩ := Finset.mem_filter.mp A.property
    rcases Set.mem_insert_iff.mp (hwitnesses hm) with hscalar | hconj
    · exact False.elim (hne hscalar)
    · obtain ⟨U, hU, hAU⟩ := hconj
      exact ⟨⟨U, hU⟩, hAU⟩
  let U (i : Fin orbitWitnesses.card) : G :=
    Classical.choose (hrep (orbitWitnesses.equivFin.symm i))
  refine ⟨orbitWitnesses.card, U, le_antisymm ?_ ?_⟩
  · change Submodule.span ℝ _ ≤ K
    rw [← hS]
    apply Submodule.span_mono
    refine Set.insert_subset_insert ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨(U i).val, (U i).property, rfl⟩
  · change K ≤ Submodule.span ℝ _
    rw [← hgenerators]
    refine (Submodule.span_le.mpr hspan).trans ?_
    apply Submodule.span_mono
    intro A hA
    by_cases ha : A = Complex.I • (1 : Mat ι)
    · exact Set.mem_insert_iff.mpr (Or.inl ha)
    let a : orbitWitnesses := ⟨A, Finset.mem_filter.mpr ⟨hA, ha⟩⟩
    apply Set.mem_insert_of_mem
    refine ⟨orbitWitnesses.equivFin a, ?_⟩
    exact (Classical.choose_spec (hrep (orbitWitnesses.equivFin.symm
      (orbitWitnesses.equivFin a)))).trans (congrArg Subtype.val
        (orbitWitnesses.equivFin.symm_apply_apply a))

#print axioms dense_conjugatesAndPhaseSpan_eq
#print axioms exists_fin_conjugates_spanning_skewAdjoint

end CriticalDepth.UnitaryAdjointSpan
