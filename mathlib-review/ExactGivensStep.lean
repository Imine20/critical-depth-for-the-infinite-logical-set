import ExactGivensBlock
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Set

/-!
# Inserting a Givens block on an arbitrary pair of rows
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix BigOperators

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Two ordered, distinct basis indices determined by a copy of Fin 2. -/
abbrev RowPair (ι : Type*) := Fin 2 ↪ ι

local instance (e : RowPair ι) : Fintype ↑((Set.range e)ᶜ : Set ι) := Fintype.ofFinite _

/-- Partition the basis into the pair and its complement. -/
def rowPairSplit (e : RowPair ι) : Fin 2 ⊕ ((Set.range e)ᶜ : Set ι) ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range e))

private theorem rowPairSplit_inl (e : RowPair ι) (i : Fin 2) :
    rowPairSplit e (Sum.inl i) = e i := rfl

private theorem rowPairSplit_inr (e : RowPair ι) (i : ↑((Set.range e)ᶜ : Set ι)) :
    rowPairSplit e (Sum.inr i) = i.val := rfl

private theorem rowPairSplit_symm_at (e : RowPair ι) (i : Fin 2) :
    (rowPairSplit e).symm (e i) = Sum.inl i := by
  rw [← rowPairSplit_inl e i, Equiv.symm_apply_apply]

private theorem rowPairSplit_symm_else (e : RowPair ι) (i : ι)
    (hi : i ∉ Set.range e) : (rowPairSplit e).symm i = Sum.inr ⟨i, hi⟩ := by
  apply (rowPairSplit e).injective
  rw [(rowPairSplit e).apply_symm_apply, rowPairSplit_inr]

def twoLevel (e : RowPair ι) (A : Operator (Fin 2)) : Operator ι :=
  reindex (rowPairSplit e) (rowPairSplit e) (fromBlocks A 0 0 (1 : Operator ((Set.range e)ᶜ : Set ι)))

/-- The nontrivial block is an exact unitary embedding. -/
theorem twoLevel_isUnitary (e : RowPair ι) (A : Operator (Fin 2)) (hA : IsUnitary A) :
    IsUnitary (twoLevel e A) := by
  classical
  let B : Operator (Fin 2 ⊕ ((Set.range e)ᶜ : Set ι)) := fromBlocks A 0 0 (1 : Operator ((Set.range e)ᶜ : Set ι))
  have hb : IsUnitary B := by
    have ha₁ : A.conjTranspose * A = 1 := hA.1
    have ha₂ : A * A.conjTranspose = 1 := hA.2
    constructor <;> simp [B, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, ha₁, ha₂, Matrix.fromBlocks_one]
  let F := reindexAlgEquiv ℂ ℂ (rowPairSplit e)
  have hF : F (star B) = star (F B) := rfl
  change IsUnitary (F B)
  constructor
  · rw [← hF, ← map_mul, hb.1, map_one]
  · rw [← hF, ← map_mul, hb.2, map_one]

theorem twoLevel_mulVec_at (e : RowPair ι) (A : Operator (Fin 2)) (v : ι → ℂ)
    (i : Fin 2) : (twoLevel e A *ᵥ v) (e i) = (A *ᵥ (v ∘ e)) i := by
  classical
  unfold twoLevel
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def, rowPairSplit_symm_at, rowPairSplit_inl]

theorem twoLevel_mulVec_else (e : RowPair ι) (A : Operator (Fin 2)) (v : ι → ℂ)
    {j : ι} (hj : j ∉ Set.range e) : (twoLevel e A *ᵥ v) j = v j := by
  classical
  unfold twoLevel
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def, rowPairSplit_symm_else e j hj, rowPairSplit_inr]

theorem twoLevel_mul_at (e : RowPair ι) (A : Operator (Fin 2)) (V : Matrix ι κ ℂ)
    (i : Fin 2) (j : κ) : (twoLevel e A * V) (e i) j = (A *ᵥ (fun a => V (e a) j)) i := by
  change (twoLevel e A *ᵥ (fun a => V a j)) (e i) = _
  exact twoLevel_mulVec_at e A _ i

theorem twoLevel_mul_else (e : RowPair ι) (A : Operator (Fin 2)) (V : Matrix ι κ ℂ)
    {i : ι} (hi : i ∉ Set.range e) (j : κ) : (twoLevel e A * V) i j = V i j := by
  change (twoLevel e A *ᵥ (fun a => V a j)) i = _
  exact twoLevel_mulVec_else e A _ hi

/-- The Givens step evaluates the two chosen entries. It uses identity
when the radius is zero. -/
def givensStep (V : Matrix ι κ ℂ) (e : RowPair ι) (j : κ) : Operator ι :=
  if givensRadius (V (e 0) j) (V (e 1) j) = 0 then 1
  else twoLevel e (givensBlock (V (e 0) j) (V (e 1) j))

theorem givensStep_isUnitary (V : Matrix ι κ ℂ) (e : RowPair ι) (j : κ) :
    IsUnitary (givensStep V e j) := by
  unfold givensStep
  split
  · exact isUnitary_one
  · rename_i hr
    exact twoLevel_isUnitary e _ (givensBlock_isUnitary _ _ hr)

theorem givensStep_eliminates (V : Matrix ι κ ℂ) (e : RowPair ι) (j : κ) :
    (givensStep V e j * V) (e 1) j = 0 := by
  unfold givensStep
  split
  · rename_i hr
    rw [Matrix.one_mul]
    exact (givensRadius_eq_zero_iff _ _).mp hr |>.2
  · rename_i hr
    rw [twoLevel_mul_at]
    have he : (fun a : Fin 2 => V (e a) j) = ![V (e 0) j, V (e 1) j] := by
      funext a
      fin_cases a <;> rfl
    rw [he, givensBlock_mulVec _ _ hr]
    rfl

/-- All other rows are unchanged by the two-level operation. -/
theorem givensStep_preserves_other_rows (V : Matrix ι κ ℂ) (e : RowPair ι) (j : κ)
    {i : ι} (hi : i ∉ Set.range e) (l : κ) :
    (givensStep V e j * V) i l = V i l := by
  unfold givensStep
  split
  · rw [Matrix.one_mul]
  · exact twoLevel_mul_else e _ V hi l

/-- The operation preserves a previously processed column if both active
rows were zero in that column. -/
theorem givensStep_preserves_zero_entries (V : Matrix ι κ ℂ) (e : RowPair ι)
    (j l : κ) (h₀ : V (e 0) l = 0) (h₁ : V (e 1) l = 0) :
    ∀ i, (givensStep V e j * V) i l = V i l := by
  classical
  intro i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    have hv : (fun u : Fin 2 => V (e u) l) = 0 := by
      funext u
      fin_cases u <;> assumption
    unfold givensStep
    split
    · rw [Matrix.one_mul]
    · rw [twoLevel_mul_at, hv, Matrix.mulVec_zero]
      exact (congrFun hv a).symm
  · exact givensStep_preserves_other_rows V e j hi l

#print axioms twoLevel_isUnitary
#print axioms givensStep_eliminates
#print axioms givensStep_preserves_zero_entries

end

end CriticalDepth.Manuscript20261114
