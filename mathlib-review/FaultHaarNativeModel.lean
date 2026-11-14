import FaultHaarOptimality
import FaultHistoryExperimentNormalization

/-!
The pure-state average uses the histories and terminal CPTP maps of the
arbitrary paper gate-list and normalized native fault models.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryNormalization CriticalDepth.FaultHistoryExperimentNormalization
open CriticalDepth.IndependentFaultHistories CriticalDepth.FaultDepthArithmetic
open scoped ENat

variable {n K q : ℕ} [Nonempty (Fin K × Fin 1)]

def circuitAverageInfidelity (C : Code n (fun _ => 2) K 1)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i)) : ℝ → ℝ :=
  optimalAverageInfidelity μ (encodedBranch C)

theorem circuitAverageInfidelity_eq_dim_ratio (C : Code n (fun _ => 2) K 1)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i)) (p : ℝ) :
    circuitAverageInfidelity C L μ p =
      fidelityDimensionRatio (Fin K × Fin 1) * circuitInfidelity C L μ p :=
  optimalAverageInfidelity_eq_dim_ratio μ _ (encodedBranch_isometry C) p

theorem circuitAverageInfidelity_exponent_eq (C : Code n (fun _ => 2) K 1)
    (L : Layers n q) (μ : Law (fun i : Location L => FaultLabel i)) :
    FaultExponent.exponent (circuitAverageInfidelity C L μ) =
      FaultExponent.exponent (circuitInfidelity C L μ) :=
  optimalAverageInfidelity_exponent_eq μ _ (encodedBranch_isometry C)

def paperCircuitAverageInfidelity (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) : ℝ → ℝ :=
  optimalAverageInfidelity μ (paperEncodedBranch C L)

theorem paperEncodedBranch_isometry (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (x : History (PaperLabel L)) :
    (paperEncodedBranch C L x).conjTranspose * paperEncodedBranch C L x = 1 := by
  rw [paperEncodedBranch_eq_native]
  exact encodedBranch_isometry C _

theorem paperCircuitAverageInfidelity_eq_dim_ratio (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) (p : ℝ) :
    paperCircuitAverageInfidelity C L μ p =
      fidelityDimensionRatio (Fin K × Fin 1) * paperCircuitInfidelity C L μ p :=
  optimalAverageInfidelity_eq_dim_ratio μ _ (paperEncodedBranch_isometry C L) p

theorem paperCircuitAverageInfidelity_eq_native (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) :
    paperCircuitAverageInfidelity C L μ =
      circuitAverageInfidelity C (normalizedLayers L) (pushLaw L μ) := by
  funext p
  rw [paperCircuitAverageInfidelity_eq_dim_ratio, circuitAverageInfidelity_eq_dim_ratio,
    paperCircuitInfidelity_eq_native]

theorem paperCircuitAverageInfidelity_exponent_eq (C : Code n (fun _ => 2) K 1)
    (L : PaperLayers (n := n) (q := q)) (μ : Law (PaperLabel L)) :
    FaultExponent.exponent (paperCircuitAverageInfidelity C L μ) =
      FaultExponent.exponent (paperCircuitInfidelity C L μ) :=
  optimalAverageInfidelity_exponent_eq μ _ (paperEncodedBranch_isometry C L)

def perCodeAverageExponent (C : Code n (fun _ => 2) K 1) (q h : ℕ) : ℕ∞ :=
  FaultExponent.worstCaseExponent fun e : Experiment C q h =>
    circuitAverageInfidelity C e.layers e.law

theorem perCodeAverageExponent_eq (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    perCodeAverageExponent C q h = perCodeExponent C q h := by
  unfold perCodeAverageExponent perCodeExponent FaultExponent.worstCaseExponent
  simp_rw [circuitAverageInfidelity_exponent_eq]

def paperPerCodeAverageExponent (C : Code n (fun _ => 2) K 1) (q h : ℕ) : ℕ∞ :=
  FaultExponent.worstCaseExponent fun e : PaperExperiment C q h =>
    paperCircuitAverageInfidelity C e.layers e.law

theorem paperPerCodeAverageExponent_eq (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    paperPerCodeAverageExponent C q h = paperPerCodeExponent C q h := by
  unfold paperPerCodeAverageExponent paperPerCodeExponent FaultExponent.worstCaseExponent
  simp_rw [paperCircuitAverageInfidelity_exponent_eq]

theorem paperPerCodeAverageExponent_eq_native (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    paperPerCodeAverageExponent C q h = perCodeAverageExponent C q h := by
  rw [paperPerCodeAverageExponent_eq, perCodeAverageExponent_eq, paperPerCodeExponent_eq_native]

theorem stabilizer_paperPerCodeAverageExponent_envelopes {k d : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hS : IsStabilizer C) (hD : HasActualDistance C d)
    (hd : 2 ≤ d) (hq : 2 ≤ q) {h : ℕ} (hh : 1 ≤ h) :
    (lowerEnvelope q d h : ℕ∞) ≤ paperPerCodeAverageExponent C q h ∧
      paperPerCodeAverageExponent C q h ≤ (upperEnvelope q d h : ℕ∞) := by
  rw [paperPerCodeAverageExponent_eq]
  exact stabilizer_paperPerCodeExponent_envelopes C hS hD hd hq hh

#print axioms circuitAverageInfidelity_eq_dim_ratio
#print axioms paperCircuitAverageInfidelity_eq_native
#print axioms perCodeAverageExponent_eq
#print axioms paperPerCodeAverageExponent_eq_native
#print axioms stabilizer_paperPerCodeAverageExponent_envelopes

end
end CriticalDepth.FaultAverageInfidelity
