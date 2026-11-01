import CriticalDepth.PauliSynthesis

/-!
# Five-qubit physical compression and depth-three synthesis

The unphased string is X ⊗ Y ⊗ Z ⊗ I ⊗ I on the complete five-qubit
register. Its weight is three. Binary compression therefore needs one
parallel layer, followed by one two-site middle gate and one inverse layer.
The calls below produce actual circuits on the 32-dimensional register.

This is a physical circuit example. It does not supply a code-distance or
stabilizer-code hypothesis. The support statements concern the evaluated
operators; they do not add a claim about every intermediate gate.
-/

noncomputable section

namespace CriticalDepth.Manuscript.PhysicalCompressionExample

open Matrix

def p : Fin 5 → SinglePauli := ![.X, .Y, .Z, .I, .I]

def activeSites : Finset (Fin 5) := {0, 1, 2}

def P : Operator (QubitBasis 5) := pauliMatrix (0 : Fin 4) p

theorem register_dimension : Fintype.card (QubitBasis 5) = 32 := by
  decide

theorem pauli_support : pauliSupport p = activeSites := by
  decide

theorem weight_three : (pauliSupport p).card = 3 := by
  rw [pauli_support]
  decide

theorem critical_depth_three :
    Arithmetic.criticalDepth 2 (pauliSupport p).card = 3 := by
  rw [weight_three]
  decide

theorem pauli_supported : SupportedOn P activeSites := by
  simpa only [P, pauli_support] using pauliMatrix_supportedOn_pauliSupport p

/-- The example is a genuine non-scalar physical Pauli operator. -/
theorem pauli_nonscalar : ¬ IsScalar P := by
  let x : QubitBasis 5 := ![0, 0, 0, 0, 0]
  let y : QubitBasis 5 := ![1, 1, 0, 0, 0]
  have hxy : x ≠ y := by decide
  have hentry : P x y = -Complex.I := by
    norm_num [P, p, x, y, pauliMatrix, SinglePauli.matrix, Fin.prod_univ_succ]
  rintro ⟨z, hz⟩
  have hh := congrArg (fun A : Operator (QubitBasis 5) => A x y) hz
  have hzero : (-Complex.I : ℂ) = 0 := by
    simpa only [hentry, Matrix.smul_apply, Matrix.one_apply, if_neg hxy, smul_zero]
      using hh
  exact Complex.I_ne_zero (neg_eq_zero.mp hzero)

/-- A real two-ary layer compresses the weight from three to two. -/
theorem one_round_compression :
    ∃ p' : Fin 5 → SinglePauli, ∃ L : Layer 5 (fun _ => 2) 2,
      L.eval * P * star L.eval = pauliMatrix (0 : Fin 4) p' ∧
        (pauliSupport p').card = 2 := by
  obtain ⟨p', L, hconj, hweight⟩ := pauli_compression_layer 2 (by decide) p
  refine ⟨p', L, ?_, ?_⟩
  · simpa only [P] using hconj
  · have hceil : Arithmetic.ceilDiv 3 2 = 2 := by decide
    simpa only [weight_three, hceil] using hweight

/-- Every real parameter has an actual depth-three two-ary circuit. -/
theorem rotation_depth_three (t : ℝ) :
    ∃ c : Circuit 5 (fun _ => 2) 2 3,
      circuitEval c = rotation P t := by
  have hd : 2 ≤ (pauliSupport p).card := by rw [weight_three]; decide
  obtain ⟨c, hc⟩ := pauli_rotation_synthesis 2 (by decide) p hd t
  refine ⟨(critical_depth_three ▸ c : Circuit 5 (fun _ => 2) 2 3), ?_⟩
  exact (circuitEval_cast (n := 5) (dim := fun _ => 2) (q := 2)
    critical_depth_three c).trans hc

theorem rotation_supported (t : ℝ) : SupportedOn (rotation P t) activeSites := by
  unfold rotation
  exact pauli_supported.affine _ _

/-- The concrete rational parameter two is synthesized at the same exact depth. -/
theorem rational_rotation_two_depth_three :
    ∃ c : Circuit 5 (fun _ => 2) 2 3,
      circuitEval c = rationalRotation P 2 := by
  have hd : 2 ≤ (pauliSupport p).card := by rw [weight_three]; decide
  obtain ⟨c, hc⟩ := pauli_rationalRotation_synthesis 2 (by decide) p hd 2
  refine ⟨(critical_depth_three ▸ c : Circuit 5 (fun _ => 2) 2 3), ?_⟩
  exact (circuitEval_cast (n := 5) (dim := fun _ => 2) (q := 2)
    critical_depth_three c).trans hc

/-- This formula follows the actual normalization used by rationalRotation. -/
theorem rational_rotation_two_formula :
    rationalRotation P 2 =
      affine P ((Real.sqrt (5 : ℝ) : ℂ)⁻¹)
        (((Real.sqrt (5 : ℝ) : ℂ)⁻¹) * Complex.I * 2) := by
  norm_num [rationalRotation, rationalScale]

theorem rational_rotation_two_isUnitary : IsUnitary (rationalRotation P 2) := by
  exact rationalRotation_isUnitary (unphased_pauliMatrix_selfAdjoint p)
    (unphased_pauliMatrix_sq p) 2

theorem rational_rotation_two_supported :
    SupportedOn (rationalRotation P 2) activeSites := by
  unfold rationalRotation
  exact pauli_supported.affine _ _

/-- A synthesized circuit has the stated output support on the full register. -/
theorem supported_rational_circuit :
    ∃ c : Circuit 5 (fun _ => 2) 2 3,
      circuitEval c = rationalRotation P 2 ∧ SupportedOn (circuitEval c) activeSites := by
  obtain ⟨c, hc⟩ := rational_rotation_two_depth_three
  refine ⟨c, hc, ?_⟩
  rw [hc]
  exact rational_rotation_two_supported

#print CriticalDepth.Manuscript.PhysicalCompressionExample.one_round_compression
#print CriticalDepth.Manuscript.PhysicalCompressionExample.rotation_depth_three
#print CriticalDepth.Manuscript.PhysicalCompressionExample.rational_rotation_two_depth_three
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.pauli_nonscalar
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.one_round_compression
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.rotation_depth_three
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.rational_rotation_two_depth_three
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.rational_rotation_two_formula
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.supported_rational_circuit

end CriticalDepth.Manuscript.PhysicalCompressionExample
