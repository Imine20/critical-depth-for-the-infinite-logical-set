import FaultAverageInfidelity
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Normalized surface measure on the real Euclidean unit sphere underlying the
logical complex Hilbert space. Its invariance under orthogonal maps includes
the physical unitary action.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := sphere (0 : E) 1

/-- The normalized spherical measure induced by Euclidean volume. -/
def sphereHaar (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Measure (UnitSphere E) :=
  ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere

instance sphereHaar_isProbability [Nontrivial E] : IsProbabilityMeasure (sphereHaar E) where
  measure_univ := by
    let μ := (volume : Measure E).toSphere
    have h0 : μ univ ≠ 0 := by
      have hμ : μ ≠ 0 := Measure.toSphere_ne_zero (volume : Measure E)
      intro h
      apply hμ
      apply Measure.ext
      intro s hs
      have he : μ s ≤ μ univ := measure_mono (subset_univ s)
      rw [h] at he
      have hs₀ : μ s = 0 := le_antisymm he (by positivity)
      simp [hs₀]
    have htop : μ univ ≠ ∞ := (measure_lt_top μ univ).ne
    change ((μ univ)⁻¹ • μ) univ = 1
    simp [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- Orthogonal maps on the ambient Euclidean space restrict to homeomorphisms
of the same unit sphere. -/
def sphereAction (U : E ≃ₗᵢ[ℝ] E) : UnitSphere E ≃ₜ UnitSphere E :=
  U.toHomeomorph.subtype (fun x => by simp only [mem_sphere_zero_iff_norm,
    LinearIsometryEquiv.coe_toHomeomorph, U.norm_map])

theorem sphereAction_apply (U : E ≃ₗᵢ[ℝ] E) (x : UnitSphere E) :
    (sphereAction U x).val = U x.val := rfl

private theorem sphereCone_preimage (U : E ≃ₗᵢ[ℝ] E) (s : Set (UnitSphere E)) :
    (Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereAction U ⁻¹' s))) =
      U ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨r, hr, U y.val, ⟨sphereAction U y, hy, rfl⟩, (U.map_smul r y.val).symm⟩
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, he⟩
    let z := (sphereAction U).symm y
    have hz : sphereAction U z = y := (sphereAction U).apply_symm_apply y
    have hzy : U z.val = y.val := congrArg Subtype.val hz
    refine ⟨r, hr, z.val, ⟨z, ?_, rfl⟩, U.injective ?_⟩
    · change sphereAction U z ∈ s
      rwa [hz]
    · rw [U.map_smul, hzy]
      exact he

/-- The normalized Haar probability is invariant under all ambient
orthogonal transformations. -/
theorem sphereAction_measurePreserving (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereAction U) (sphereHaar E) (sphereHaar E) := by
  let μ := (volume : Measure E).toSphere
  have hSphere : Measure.map (sphereAction U) μ = μ := by
    apply Measure.ext
    intro s hs
    have hmeas := (sphereAction U).measurable
    rw [Measure.map_apply hmeas hs]
    change (volume : Measure E).toSphere (sphereAction U ⁻¹' s) =
      (volume : Measure E).toSphere s
    rw [Measure.toSphere_apply' _ (hmeas hs), Measure.toSphere_apply' _ hs,
      sphereCone_preimage]
    rw [U.measurePreserving.measure_preimage_emb U.toMeasurableEquiv.measurableEmbedding]
  refine ⟨(sphereAction U).measurable, ?_⟩
  change Measure.map (sphereAction U) ((μ univ)⁻¹ • μ) = (μ univ)⁻¹ • μ
  rw [Measure.map_smul _ (sphereAction U).measurable.aemeasurable, hSphere]

theorem integral_sphereAction (U : E ≃ₗᵢ[ℝ] E)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : UnitSphere E → V) :
    (∫ x, f (sphereAction U x) ∂sphereHaar E) = ∫ x, f x ∂sphereHaar E :=
  (sphereAction_measurePreserving U).integral_comp (sphereAction U).measurableEmbedding f

theorem sphereHaar_integrable_continuous {V : Type*} [NormedAddCommGroup V]
    (f : UnitSphere E → V) (hf : Continuous f) : Integrable f (sphereHaar E) := by
  letI : CompactSpace (UnitSphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  letI : IsFiniteMeasure (sphereHaar E) := by
    refine ⟨?_⟩
    unfold sphereHaar
    rw [Measure.smul_apply, smul_eq_mul]
    by_cases h : (volume : Measure E).toSphere univ = 0
    · simp [h]
    · have htop : ((volume : Measure E).toSphere univ) ≠ ∞ := measure_ne_top _ _
      rw [ENNReal.inv_mul_cancel h htop]
      simp
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

#print axioms sphereHaar_isProbability
#print axioms sphereAction_measurePreserving
#print axioms integral_sphereAction
#print axioms sphereHaar_integrable_continuous

end
end CriticalDepth.FaultAverageInfidelity
