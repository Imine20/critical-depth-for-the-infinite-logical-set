import OneQubitEuler
import UnitaryCurveProducts

/-!
# A local projective generation criterion for one qubit
-/

open scoped Matrix.Norms.Frobenius

namespace CriticalDepth.Manuscript20261114.CliffordT

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114.OneQubitEuler
open Filter Set

variable {τ : Type*} [Fintype τ]

private theorem all_curve_mem_of_isClopen
    (G : Subgroup (PU (Fin 2))) (hG : IsClopen (G : Set (PU (Fin 2))))
    (c : ℝ → PU (Fin 2)) (hc : Continuous c) (h0 : c 0 = 1) :
    ∀ t, c t ∈ G := by
  have hNonempty : (c ⁻¹' (G : Set (PU (Fin 2)))).Nonempty :=
    ⟨0, by change c 0 ∈ G; rw [h0]; exact G.one_mem⟩
  have ho := (hG.preimage hc).eq_univ hNonempty
  intro t
  change t ∈ c ⁻¹' (G : Set (PU (Fin 2)))
  rw [ho]
  exact mem_univ t

/-- A closed subgroup of qubit projective unitaries containing curves
with spanning tangent directions equals the whole group. -/
theorem eq_top_of_closed_spanning_unitary_curves
    (G : Subgroup (PU (Fin 2))) (hG : IsClosed (G : Set (PU (Fin 2))))
    (c : τ → ℝ → Matrix.unitaryGroup (Fin 2) ℂ)
    (h0 : ∀ i, c i 0 = 1)
    (hmem : ∀ i t, projectiveMk (Fin 2) (c i t) ∈ G)
    (hSmooth : ∀ i, ContDiffAt ℝ 1 (fun t => (c i t).val) 0)
    (X : τ → Operator (Fin 2))
    (hDeriv : ∀ i, HasDerivAt (fun t => (c i t).val) (X i) 0)
    (hSpan : skewAdjoint.submodule ℝ (Operator (Fin 2)) ≤ Submodule.span ℝ (Set.range X)) :
    G = ⊤ := by
  let up := G.comap (projectiveMk (Fin 2))
  have hN := UnitaryCurveProducts.one_nhds_of_unitaryCurveProducts up c h0 hmem hSmooth X hDeriv hSpan
  have hOpenMap : IsOpenMap (projectiveMk (Fin 2)) := QuotientGroup.isOpenMap_coe
  have hImage := hOpenMap.image_mem_nhds hN
  rw [map_one] at hImage
  have hOpen : IsOpen (G : Set (PU (Fin 2))) := by
    apply G.isOpen_of_mem_nhds
    apply Filter.mem_of_superset hImage
    rintro x ⟨u, hu, rfl⟩
    exact hu
  have hClopen : IsClopen (G : Set (PU (Fin 2))) := ⟨hG, hOpen⟩
  apply subgroup_eq_top_of_has_XZ
  · apply all_curve_mem_of_isClopen G hClopen projectiveX
    · exact (continuous_projectiveMk (ι := Fin 2)).comp (continuous_unitaryRotation _ _ _)
    · unfold projectiveX projectiveRotation
      rw [show unitaryRotation SinglePauli.X.matrix _ _ 0 = 1 from Subtype.ext (rotation_zero _), map_one]
  · apply all_curve_mem_of_isClopen G hClopen projectiveZ
    · exact (continuous_projectiveMk (ι := Fin 2)).comp (continuous_unitaryRotation _ _ _)
    · unfold projectiveZ projectiveRotation
      rw [show unitaryRotation SinglePauli.Z.matrix _ _ 0 = 1 from Subtype.ext (rotation_zero _), map_one]

#print axioms eq_top_of_closed_spanning_unitary_curves

end CriticalDepth.Manuscript20261114.CliffordT
