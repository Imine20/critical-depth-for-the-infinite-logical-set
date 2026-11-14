import CriticalDepthMathlib

/-!
# A common vacuum for an abstract logical Pauli frame
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable [Fintype ι] [DecidableEq ι]

/-- Commuting Z observables and their independent X flips. The Hilbert
dimension is used only when we turn the orbit into a complete basis. -/
structure LogicalPauliFrame (ι α : Type*) [Fintype α] [DecidableEq α] where
  X : ι → Operator α
  Z : ι → Operator α
  xSelf : ∀ i, star (X i) = X i
  zSelf : ∀ i, star (Z i) = Z i
  xSq : ∀ i, X i * X i = 1
  zSq : ∀ i, Z i * Z i = 1
  xx : ∀ i j, Commute (X i) (X j)
  zz : ∀ i j, Commute (Z i) (Z j)
  zx_same : ∀ i, Z i * X i = -(X i * Z i)
  zx_other : ∀ i j, i ≠ j → Commute (Z i) (X j)

private theorem commute_on_mulVec (A B : Operator α) (h : Commute A B)
    (v : α → ℂ) : A *ᵥ (B *ᵥ v) = B *ᵥ (A *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.eq]

private theorem mulVec_mulVec_neg_of_anticommute (A B : Operator α)
    (h : A * B = -(B * A)) (v : α → ℂ) :
    A *ᵥ (B *ᵥ v) = -(B *ᵥ (A *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, h, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]

/-- Without checking eigenvalue multiplicities in advance, produce a
nonzero vector stabilized by any specified set of Z operators. -/
theorem LogicalPauliFrame.exists_joint_fixed_nonzero (F : LogicalPauliFrame ι α)
    (S : Finset ι) :
    ∃ v : α → ℂ, v ≠ 0 ∧ ∀ i ∈ S, F.Z i *ᵥ v = v := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, one_ne_zero, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨v, hv, hfix⟩ := ih
    let w := v + F.Z i *ᵥ v
    by_cases hw : w = 0
    · have hneg : F.Z i *ᵥ v = -v := by
        exact eq_neg_of_add_eq_zero_right hw
      refine ⟨F.X i *ᵥ v, ?_, ?_⟩
      · intro hz
        apply hv
        calc
          v = F.X i *ᵥ (F.X i *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, F.xSq, Matrix.one_mulVec]
          _ = 0 := by rw [hz, Matrix.mulVec_zero]
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [mulVec_mulVec_neg_of_anticommute _ _ (F.zx_same _), hneg,
            Matrix.mulVec_neg, neg_neg]
        · rw [commute_on_mulVec _ _ (F.zx_other j i (fun h => hi (h ▸ hj))), hfix _ hj]
    · refine ⟨w, hw, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · dsimp [w]
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, F.zSq, Matrix.one_mulVec, add_comm]
      · dsimp [w]
        rw [Matrix.mulVec_add, commute_on_mulVec _ _ (F.zz j i), hfix _ hj]

/-- A +1 eigenvector for all logical Z axes. -/
theorem LogicalPauliFrame.exists_vacuum (F : LogicalPauliFrame ι α) :
    ∃ v : α → ℂ, v ≠ 0 ∧ ∀ i, F.Z i *ᵥ v = v := by
  obtain ⟨v, hv, hf⟩ := F.exists_joint_fixed_nonzero Finset.univ
  exact ⟨v, hv, fun i => hf i (Finset.mem_univ i)⟩

#print axioms LogicalPauliFrame.exists_vacuum

end CriticalDepth.Manuscript20261114
