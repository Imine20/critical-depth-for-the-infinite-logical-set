import MidpointLogicalCeiling
import FaultOnsetConsequence
import ShorFaultWitnessAmbiguity

/-! An explicit implementation has linear optimal error above the later onset. -/

namespace CriticalDepth.FaultNativeCeiling

open Filter CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.MidpointFaultWitness CriticalDepth.IndependentFaultHistories
open CriticalDepth.EncodedFaultRecovery
open scoped Kronecker ENat Topology

theorem exists_linear_failure_above_upperOnset {n k d q h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hS : IsStabilizer C) (hD : HasActualDistance C d)
    (hq : 2 ≤ q) (hd : 2 * q < d) (hh : 1 ≤ h) (hh₀ : upperOnset q d ≤ h) :
    ∃ e : Experiment C q h,
      (circuitInfidelity C e.layers e.law =O[𝓝[>] 0] fun p => p) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ), a * p ≤ circuitInfidelity C e.layers e.law p := by
  obtain ⟨e, _, hTrace, x, y, hxy, hx, hy, _, hAmb⟩ :=
    exists_logicalPauli_midpoint_histories C hS hD q h (by omega) hq hh
  have hceil : upperEnvelope q d h = 1 := (upperEnvelope_eq_one_iff q d h hq hd).mpr hh₀
  let W := e.logical ⊗ₖ (1 : Operator (Fin 1))
  have hW : W * W.conjTranspose = 1 :=
    (point_kronecker_isUnitary e.logical 1 e.exactAction.1 isUnitary_one).2
  have htr : W.trace = 0 := by
    change (e.logical ⊗ₖ (1 : Operator (Fin 1))).trace = 0
    rw [Matrix.trace_kronecker, hTrace, zero_mul]
  have hcnt : max (faults x).card (faults y).card = 1 := by
    have hw : ceilDiv (ceilDiv d (q ^ ceilHalf h)) 2 = 1 :=
      (midpointHistoryCount q d h).trans hceil
    have hbound := (ceilDiv_le_iff _ _ _ (by decide : 0 < (2 : ℕ))).mp hw.le
    rw [hx, hy, hceil]
    exact max_eq_right (by omega)
  have hamb := CriticalDepth.ShorFaultWitnessAmbiguity.two_history_eventual_lower e.law
    (encodedBranch C) (encodedBranch_isometry C) x y hxy W hW htr hAmb
  obtain ⟨a, ha, h⟩ := hamb
  have hLower : ∀ᶠ p in 𝓝[>] (0 : ℝ), a * p ≤ circuitInfidelity C e.layers e.law p := by
    simpa only [hcnt, pow_one, circuitInfidelity] using h
  have hFloor := native_circuit_exponent_floor C d hD.1 e.layers e.law (by omega) e.logical e.exactAction
  have hpos : (1 : ℕ∞) ≤ (lowerEnvelope q d e.layers.length : ℕ∞) := by
    exact_mod_cast (ceilDiv_pos (show 0 < d by omega) (q ^ e.layers.length + q))
  have hUpper := FaultExponent.exponent_le_of_powerLower ha 1 (by simpa only [pow_one] using hLower)
  refine ⟨e, ?_, a, ha, hLower⟩
  simpa only [pow_one] using
    FaultExponent.isBigO_of_exponent_eq (m := 1) (le_antisymm hUpper (hpos.trans hFloor)) (by decide)

#print axioms exists_linear_failure_above_upperOnset

end CriticalDepth.FaultNativeCeiling
