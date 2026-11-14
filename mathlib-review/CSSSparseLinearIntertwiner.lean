import CSSSparseLinearUnchanged
import CSSRandomXChecks

/-!
A linear symmetry preserving the planted span yields an intertwining matrix
on the generator coefficients. A trivial coefficient action forces the
physical symmetry to be trivial by the dual distance.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped Matrix BigOperators

local notation "𝔽" => ZMod 2
variable {n a : ℕ}

theorem exists_intertwiner_of_range_preservation
    (F : Matrix (Fin n) (Fin n) 𝔽) (A : (Fin a → 𝔽) →ₗ[𝔽] BW n)
    (hA : Function.Injective A) (hF : F.mulVec '' (A.range : Set (BW n)) ⊆ A.range) :
    ∃ S : Matrix (Fin a) (Fin a) 𝔽, F * A.toMatrix' = A.toMatrix' * S := by
  let E := LinearEquiv.ofInjective A hA
  let R : A.range →ₗ[𝔽] A.range :=
    (F.mulVecLin.comp A.range.subtype).codRestrict A.range
      (fun x => hF ⟨x.val, x.property, rfl⟩)
  let S : (Fin a → 𝔽) →ₗ[𝔽] Fin a → 𝔽 := E.symm.toLinearMap.comp (R.comp E.toLinearMap)
  refine ⟨S.toMatrix', ?_⟩
  have hcomp : F.mulVecLin.comp A = A.comp S := by
    apply LinearMap.ext
    intro x
    change F.mulVecLin (A x) = A (E.symm (R (E x)))
    have ht : A (E.symm (R (E x))) = (R (E x)).val := by
      exact congrArg (fun y : A.range => y.val) (E.apply_symm_apply (R (E x)))
    rw [ht]
    rfl
  have he := congrArg LinearMap.toMatrix' hcomp
  simpa only [LinearMap.toMatrix'_comp, show F.mulVecLin.toMatrix' = F from
    LinearMap.toMatrix'_toLin' F] using he

theorem sparse_linear_eq_one_of_trivial_intertwiner
    (F : Matrix (Fin n) (Fin n) 𝔽) (A : (Fin a → 𝔽) →ₗ[𝔽] BW n) (R : ℕ)
    (hRow : ∀ i, wordWeight (F.row i) ≤ R)
    (hdual : ∀ v ∈ cssOrthogonal A.range, v ≠ 0 → R + 1 < wordWeight v)
    (hA : F * A.toMatrix' = A.toMatrix' * (1 : Matrix (Fin a) (Fin a) 𝔽)) : F = 1 := by
  rw [Matrix.mul_one] at hA
  ext i j
  let v : BW n := (F - 1).row i
  have hv : v ∈ cssOrthogonal A.range := by
    rw [cssOrthogonal_mem]
    rintro _ ⟨u, rfl⟩
    have hFA := congrArg (fun M : Matrix (Fin n) (Fin a) 𝔽 => M *ᵥ u) hA
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at hFA
    change F *ᵥ A u = A u at hFA
    change ((F - 1) *ᵥ A u) i = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hFA, sub_self]
    rfl
  have hweight : wordWeight v ≤ R + 1 := by
    let T := rowVariables F i
    have hSupp (k : Fin n) (hk : k ∉ T) : v k = 0 := by
      have hki : k ≠ i := fun h => hk (h.symm ▸ Finset.mem_insert_self _ _)
      have hz : F i k = 0 := by
        by_contra hn
        exact hk (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
      change F i k - (1 : Matrix (Fin n) (Fin n) 𝔽) i k = 0
      simp [Matrix.one_apply, hz, hki.symm]
    exact (wordWeight_le_of_supported hSupp).trans
      ((rowVariables_card F i).trans (Nat.succ_le_succ (hRow i)))
  have hzero : v = 0 := by
    by_contra hn
    exact (not_lt_of_ge hweight) (hdual v hv hn)
  exact sub_eq_zero.mp (congrFun hzero j)

#print axioms exists_intertwiner_of_range_preservation
#print axioms sparse_linear_eq_one_of_trivial_intertwiner

end CriticalDepth.Manuscript20261114.CSSCheckSpaces