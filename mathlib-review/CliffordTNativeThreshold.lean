import OneQubitBareSynthesis
import CliffordTDensity

/-!
# Dense and exact generation from two named depth-one qubit gates
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 OneQubitEuler
open scoped ENat

variable {n g : ℕ} {dim : Fin n → ℕ}
variable (C : Code n dim 2 g)

theorem native_depth_one_dense_of_D_B
    (q : ℕ) (hD : projectiveD ∈ nativeLogicalImage C.encoding q 1)
    (hB : projectiveB ∈ nativeLogicalImage C.encoding q 1) :
    (generatedLogicalSubgroup C.encoding q 1).topologicalClosure = ⊤ :=
  dense_of_contains_D_B (generatedLogicalSubgroup C.encoding q 1)
    (Subgroup.subset_closure hD) (Subgroup.subset_closure hB)

theorem nativeExactDepth_le_of_D_B_Z
    (q h : ℕ) (hh : 1 ≤ h)
    (hD : projectiveD ∈ nativeLogicalImage C.encoding q 1)
    (hB : projectiveB ∈ nativeLogicalImage C.encoding q 1)
    (hZ : ∀ t, projectiveZ t ∈ nativeLogicalImage C.encoding q h) :
    nativeExactDepth C.encoding q ≤ (h : ℕ∞) := by
  let G := generatedLogicalSubgroup C.encoding q h
  have hD' : projectiveD ∈ G := generatedLogicalSubgroup_mono C.encoding q hh
    (Subgroup.subset_closure hD)
  have hB' : projectiveB ∈ G := generatedLogicalSubgroup_mono C.encoding q hh
    (Subgroup.subset_closure hB)
  have hH : projectiveHadamard ∈ G := by
    rw [← projectiveD_sq_mul_B_mul_D_sq]
    exact G.mul_mem (G.mul_mem (G.pow_mem hD' 2) hB') (G.pow_mem hD' 2)
  have hz (t : ℝ) : projectiveZ t ∈ G := Subgroup.subset_closure (hZ t)
  have hx (t : ℝ) : projectiveX t ∈ G := by
    rw [← projectiveHadamard_conjugates_rotationZ]
    exact G.mul_mem (G.mul_mem hH (hz t)) (G.inv_mem hH)
  exact (nativeExactDepth_le_nat_iff C.encoding q h).mpr
    ⟨hh, subgroup_eq_top_of_has_XZ G hx hz⟩

#print axioms native_depth_one_dense_of_D_B
#print axioms nativeExactDepth_le_of_D_B_Z

end CriticalDepth.Manuscript20261114.CliffordT
