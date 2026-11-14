import OneQubitEuler
import GenerationThresholds
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Dense powers of a projective Pauli-axis rotation
-/

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.Manuscript20261114.OneQubitEuler
open Set

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard circle has dense integer powers of the exponential of
twice an irrational projective angle. -/
theorem denseRange_exp_zpow {θ : ℝ} (hθ : Irrational (θ / Real.pi)) :
    DenseRange (fun j : ℤ => Circle.exp (2 * θ) ^ j) := by
  have hIrr : Irrational ((2 * θ) / (2 * Real.pi)) := by
    rw [show (2 * θ) / (2 * Real.pi) = θ / Real.pi by ring]
    exact hθ
  have hd := AddCircle.denseRange_zsmul_coe_iff.mpr hIrr
  have hc := (AddCircle.homeomorphCircle').surjective.denseRange.comp hd
    (AddCircle.homeomorphCircle').continuous
  have hEq :
      AddCircle.homeomorphCircle' ∘ (fun j : ℤ => j • ((2 * θ : ℝ) : AddCircle (2 * Real.pi))) =
        (fun j : ℤ => Circle.exp (2 * θ) ^ j) := by
    funext j
    change AddCircle.homeomorphCircle' (j • ((2 * θ : ℝ) : AddCircle (2 * Real.pi))) = _
    rw [← AddCircle.coe_zsmul, AddCircle.homeomorphCircle'_apply_mk, Circle.exp_zsmul]
  exact hEq ▸ hc

/-- If a subgroup contains one irrational-angle rotation, its closure
contains the entire continuous rotation circle. -/
theorem circleRotationSubgroup_le_topologicalClosure_of_irrational
    (G : Subgroup (PU ι))
    (P : Operator ι) (hself : star P = P) (hsq : P * P = 1)
    (θ : ℝ) (hθ : Irrational (θ / Real.pi))
    (hMem : projectiveRotation P hself hsq θ ∈ G) :
    circleRotationSubgroup P hself hsq ≤ G.topologicalClosure := by
  let F := circleProjectiveHom P hself hsq
  have hf : Continuous F := continuous_circleProjectiveHom P hself hsq
  have hbase : F (Circle.exp (2 * θ)) ∈ G := by
    rw [show F (Circle.exp (2 * θ)) = projectiveRotation P hself hsq θ from
      circleProjectiveHom_exp_two_mul P hself hsq θ]
    exact hMem
  have hclosed : IsClosed (F ⁻¹' (G.topologicalClosure : Set (PU ι))) :=
    (Subgroup.isClosed_topologicalClosure G).preimage hf
  have hpow : Set.range (fun j : ℤ => Circle.exp (2 * θ) ^ j) ⊆
      F ⁻¹' (G.topologicalClosure : Set (PU ι)) := by
    rintro _ ⟨j, rfl⟩
    change F (Circle.exp (2 * θ) ^ j) ∈ G.topologicalClosure
    rw [map_zpow]
    exact G.le_topologicalClosure (G.zpow_mem hbase j)
  have hAll : (Set.univ : Set Circle) ⊆
      F ⁻¹' (G.topologicalClosure : Set (PU ι)) := by
    have h := (denseRange_exp_zpow hθ).closure_range
    rw [← h]
    exact closure_minimal hpow hclosed
  rintro _ ⟨z, rfl⟩
  exact hAll trivial

/-- A projective subgroup containing both logical Pauli circles is total,
by the exact Euler decomposition. -/
theorem subgroup_eq_top_of_has_circles_XZ (G : Subgroup (PU (Fin 2)))
    (hX : ∀ t, projectiveX t ∈ G) (hZ : ∀ t, projectiveZ t ∈ G) : G = ⊤ :=
  subgroup_eq_top_of_has_XZ G hX hZ

#print axioms denseRange_exp_zpow
#print axioms circleRotationSubgroup_le_topologicalClosure_of_irrational

end

end CriticalDepth.Manuscript20261114.CliffordT
