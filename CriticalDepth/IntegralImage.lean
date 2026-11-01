import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
Integral coordinates have a finite evaluation image over a field. This is a
finishing lemma for the proposed algebraic proof of manuscript Theorem 1.
Integrality of the actual circuit coordinates remains a separate obligation;
the lemma does not assume or assert the manuscript's finite-image conclusion.
-/

noncomputable section

namespace CriticalDepth

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

theorem integral_evaluation_range_finite (r : R) (hr : IsIntegral F r) :
    (Set.range fun f : R →ₐ[F] F => f r).Finite := by
  obtain ⟨p, hp, hpr⟩ := hr
  apply (Polynomial.finite_setOfPred_isRoot hp.ne_zero).subset
  rintro z ⟨f, rfl⟩
  change Polynomial.aeval (f r) p = 0
  rw [Polynomial.aeval_algHom_apply]
  change f (Polynomial.eval₂ (algebraMap F R) r p) = 0
  rw [hpr, map_zero]

theorem integral_coordinate_evaluation_image_finite {ι : Type*} [Fintype ι]
    (r : ι → R) (hr : ∀ i, IsIntegral F (r i)) :
    (Set.range fun f : R →ₐ[F] F => fun i => f (r i)).Finite := by
  classical
  let S : ι → Set F := fun i => Set.range fun f : R →ₐ[F] F => f (r i)
  have hS : ∀ i, (S i).Finite := fun i => integral_evaluation_range_finite (r i) (hr i)
  letI (i : ι) : Fintype (S i) := (hS i).fintype
  have hfinite : (Set.range fun v : (i : ι) → S i => fun i => (v i).1).Finite :=
    Set.finite_range _
  apply hfinite.subset
  rintro v ⟨f, rfl⟩
  exact ⟨fun i => ⟨f (r i), ⟨f, rfl⟩⟩, rfl⟩

end CriticalDepth
