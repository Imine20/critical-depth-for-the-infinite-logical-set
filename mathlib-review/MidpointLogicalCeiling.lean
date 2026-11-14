import MidpointExactFaultWitness

/-! The actual logical-Pauli circuit gives the universal fault ceiling. -/

namespace CriticalDepth.FaultNativeCeiling

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.EncodedFaultRecovery CriticalDepth.IndependentFaultHistories
open CriticalDepth.MidpointFaultWitness
open scoped ENat Kronecker Topology

theorem perCodeExponent_ceiling_of_logicalPauli {n k d q h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hS : IsStabilizer C) (hD : HasActualDistance C d)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    perCodeExponent C q h ≤ (upperEnvelope q d h : ℕ∞) := by
  obtain ⟨e, _, hTrace, x, y, hxy, hx, hy, _, hAmb⟩ :=
    exists_logicalPauli_midpoint_histories C hS hD q h hd hq hh
  let W := e.logical ⊗ₖ (1 : Operator (Fin 1))
  have hW : W * W.conjTranspose = 1 :=
    (point_kronecker_isUnitary e.logical 1 e.exactAction.1 isUnitary_one).2
  have htr : W.trace = 0 := by
    change (e.logical ⊗ₖ (1 : Operator (Fin 1))).trace = 0
    rw [Matrix.trace_kronecker, hTrace, zero_mul]
  have hExp := ambiguous_exponent_of_traceless_unitary e.law (encodedBranch C)
    (encodedBranch_isometry C) x y hxy W hW htr hAmb
  have hcnt : max (faults x).card (faults y).card = upperEnvelope q d h := by
    rw [hx, hy, ← midpointHistoryCount q d h]
    apply max_eq_right
    let w := ceilDiv d (q ^ ceilHalf h)
    change w / 2 ≤ ceilDiv w 2
    have hw : 0 < w := ceilDiv_pos (by omega) _
    rw [ceilDiv_of_pos hw]
    omega
  rw [hcnt] at hExp
  exact (iInf_le _ e).trans hExp

#print axioms perCodeExponent_ceiling_of_logicalPauli

end CriticalDepth.FaultNativeCeiling
