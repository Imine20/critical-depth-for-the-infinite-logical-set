import LogicalPauliVacuum
import Mathlib.Data.Finset.NoncommProd

/-!
# The simultaneous eigenvectors of a logical Pauli frame
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix

noncomputable section

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
variable (F : LogicalPauliFrame ι α)

/-- Ordered product of commuting frame flips at the indicated sites. -/
def LogicalPauliFrame.xProduct (S : Finset ι) : Operator α :=
  S.noncommProd F.X (fun i _ j _ _ => F.xx i j)

private theorem xProduct_insert (S : Finset ι) (i : ι) (hi : i ∉ S) :
    F.xProduct (insert i S) = F.X i * F.xProduct S := by
  unfold LogicalPauliFrame.xProduct
  exact Finset.noncommProd_insert_of_notMem S i F.X
    (fun a _ b _ _ => F.xx a b) hi

private theorem xProduct_empty : F.xProduct ∅ = 1 := rfl

theorem LogicalPauliFrame.xProduct_isUnitary (S : Finset ι) :
    IsUnitary (F.xProduct S) := by
  induction S using Finset.induction_on with
  | empty => rw [xProduct_empty]; exact isUnitary_one
  | @insert i S hi ih =>
    rw [xProduct_insert F S i hi]
    have hX : IsUnitary (F.X i) := by constructor <;> rw [F.xSelf, F.xSq]
    exact unitary_mul hX ih

/-- A coordinate flip toggles the corresponding factor in the Pauli word. -/
theorem LogicalPauliFrame.x_mul_xProduct_toggle (S : Finset ι) (i : ι) :
    F.X i * F.xProduct S =
      F.xProduct (if i ∈ S then S.erase i else insert i S) := by
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, ← Finset.insert_erase hi, xProduct_insert F _ _ (Finset.notMem_erase _ _),
      ← Matrix.mul_assoc, F.xSq, Matrix.one_mul]
    rw [Finset.erase_insert (Finset.notMem_erase _ _)]
  · rw [ite_eq_right hi, xProduct_insert F S i hi]

/-- All product states have the correct Z signs. -/
theorem LogicalPauliFrame.z_mulVec_xProduct (S : Finset ι) (i : ι)
    (v : α → ℂ) (hv : ∀ j, F.Z j *ᵥ v = v) :
    F.Z i *ᵥ (F.xProduct S *ᵥ v) =
      (if i ∈ S then (-1 : ℂ) else 1) • (F.xProduct S *ᵥ v) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [xProduct_empty, Matrix.one_mulVec, ite_eq_right (Finset.notMem_empty i), one_smul]
    exact hv i
  | @insert j S hj ih =>
    rw [xProduct_insert F S j hj, ← Matrix.mulVec_mulVec]
    by_cases hij : i = j
    · subst j
      have he : F.Z i *ᵥ (F.xProduct S *ᵥ v) = F.xProduct S *ᵥ v := by
        simpa [hj] using ih
      rw [Matrix.mulVec_mulVec, F.zx_same, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
        he, ite_eq_left (Finset.mem_insert_self i S), neg_one_smul]
    · rw [Matrix.mulVec_mulVec, (F.zx_other i j hij).eq, ← Matrix.mulVec_mulVec,
        ih, Matrix.mulVec_smul]
      simp [hij]

private def frameDot (x y : α → ℂ) : ℂ := star x ⬝ᵥ y

private theorem frameDot_apply_adjoint (A : Operator α) (v w : α → ℂ) :
    frameDot (A *ᵥ v) w = frameDot v (A.conjTranspose *ᵥ w) := by
  simp only [frameDot, Matrix.star_mulVec, dotProduct_mulVec]

/-- Isometry of every product of frame flips. -/
theorem LogicalPauliFrame.xProduct_orthogonal_norm (S : Finset ι) (v : α → ℂ) :
    star (F.xProduct S *ᵥ v) ⬝ᵥ (F.xProduct S *ᵥ v) = star v ⬝ᵥ v := by
  change frameDot (F.xProduct S *ᵥ v) (F.xProduct S *ᵥ v) = frameDot v v
  rw [frameDot_apply_adjoint, Matrix.mulVec_mulVec]
  have h : (F.xProduct S).conjTranspose * F.xProduct S = 1 :=
    (F.xProduct_isUnitary S).1
  rw [h, Matrix.one_mulVec]

/-- Distinct subsets of flips give orthogonal common Z eigenvectors. -/
theorem LogicalPauliFrame.xProduct_orthogonal_distinct (S T : Finset ι) (hST : S ≠ T)
    (v : α → ℂ) (hv : ∀ j, F.Z j *ᵥ v = v) :
    star (F.xProduct S *ᵥ v) ⬝ᵥ (F.xProduct T *ᵥ v) = 0 := by
  classical
  have hDiff : ∃ i : ι, ¬ (i ∈ S ↔ i ∈ T) := by
    by_contra! h
    exact hST (Finset.ext h)
  obtain ⟨i, hi⟩ := hDiff
  let x := F.xProduct S *ᵥ v
  let y := F.xProduct T *ᵥ v
  have h : frameDot (F.Z i *ᵥ x) y = frameDot x (F.Z i *ᵥ y) := by
    rw [frameDot_apply_adjoint, ← Matrix.star_eq_conjTranspose, F.zSelf]
  have hs := F.z_mulVec_xProduct S i v hv
  have ht := F.z_mulVec_xProduct T i v hv
  change F.Z i *ᵥ x = _ at hs
  change F.Z i *ᵥ y = _ at ht
  rw [hs, ht] at h
  change frameDot x y = 0
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · exact (hi (by simp [hiS, hiT])).elim
  · simp [frameDot, hiS, hiT, neg_dotProduct] at h
    unfold frameDot
    linear_combination -(1 / 2 : ℂ) * h
  · simp [frameDot, hiS, hiT, dotProduct_neg] at h
    unfold frameDot
    linear_combination (1 / 2 : ℂ) * h
  · exact (hi (by simp [hiS, hiT])).elim

#print axioms LogicalPauliFrame.x_mul_xProduct_toggle
#print axioms LogicalPauliFrame.z_mulVec_xProduct
#print axioms LogicalPauliFrame.xProduct_orthogonal_distinct

end

end CriticalDepth.Manuscript20261114
