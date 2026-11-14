import ExactPauliParityCircuit
import CliffordTWords
import FaultOnSiteSupport

/-!
# Local Clifford basis changes for exact tensor-Pauli parity rotation
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.FaultSupportPreserving Matrix
open CriticalDepth.Manuscript20261114.CliffordT

noncomputable section

/-- A local Clifford sending a selected Z axis to its named Pauli. -/
def axisClifford : SinglePauli → Operator (Fin 2)
  | .I => 1
  | .X => hadamardMatrix
  | .Y => rotation SinglePauli.Z.matrix (-Real.pi / 4) * hadamardMatrix
  | .Z => 1

theorem axisClifford_isUnitary (p : SinglePauli) : IsUnitary (axisClifford p) := by
  cases p with
  | I => exact isUnitary_one
  | X => exact hadamardUnitary.property
  | Y =>
    exact unitary_mul
      (rotation_isUnitary (singlePauli_selfAdjoint .Z) (singlePauli_sq .Z) _)
      hadamardUnitary.property
  | Z => exact isUnitary_one

private theorem axisClifford_Y_action :
    rotation SinglePauli.Z.matrix (-Real.pi / 4) * SinglePauli.X.matrix *
      star (rotation SinglePauli.Z.matrix (-Real.pi / 4)) = SinglePauli.Y.matrix := by
  rw [star_rotation (singlePauli_selfAdjoint .Z), neg_div, neg_neg]
  let a : ℂ := (Real.sqrt 2 / 2 : ℝ)
  have ha : a ^ 2 = 1 / 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h' : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by nlinarith
    have hc := congrArg (fun x : ℝ => (x : ℂ)) h'
    simpa [a] using hc
  have hc : (Real.cos (Real.pi / 4) : ℂ) = a := by rw [Real.cos_pi_div_four]
  have hs : (Real.sin (Real.pi / 4) : ℂ) = a := by rw [Real.sin_pi_div_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotation, affine, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, hc, hs,
      SinglePauli.matrix, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two, smul_eq_mul] <;>
    simp [Matrix.one_apply] <;>
    ring_nf <;> try simp only [Complex.I_sq] <;>
    first | linear_combination 2 * Complex.I * ha | linear_combination -2 * Complex.I * ha

/-- The local basis change takes Z to the requested nonidentity Pauli. -/
theorem axisClifford_maps_Z (p : SinglePauli) (h : p ≠ .I) :
    axisClifford p * SinglePauli.Z.matrix * star (axisClifford p) = p.matrix := by
  cases p with
  | I => exact (h rfl).elim
  | X =>
    change hadamardMatrix * SinglePauli.Z.matrix * star hadamardMatrix = _
    rw [hadamardMatrix_selfAdjoint, hadamard_conjugates_Z]
  | Y =>
    change (_ * hadamardMatrix) * SinglePauli.Z.matrix * star (_ * hadamardMatrix) = _
    rw [star_mul, hadamardMatrix_selfAdjoint]
    let R := rotation SinglePauli.Z.matrix (-Real.pi / 4)
    change R * hadamardMatrix * SinglePauli.Z.matrix * (hadamardMatrix * star R) = _
    calc
      _ = R * (hadamardMatrix * SinglePauli.Z.matrix * hadamardMatrix) * star R := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hadamard_conjugates_Z]
        exact axisClifford_Y_action
  | Z => simp [axisClifford]

variable {k : ℕ}

/-- A register of one-site Clifford changes takes the Z word on the
support to the original Pauli word exactly. -/
theorem tensorAxisClifford_maps_supportZ (p : Fin k → SinglePauli) :
    let V := tensorEntries fun i => axisClifford (p i)
    V * pauliMatrix 0 (zSubset (pauliSupport p)) * star V = pauliMatrix 0 p := by
  have hc (i : Fin k) :
      axisClifford (p i) * (zSubset (pauliSupport p) i).matrix *
        star (axisClifford (p i)) = (p i).matrix := by
    by_cases h : p i = .I
    · simp [zSubset, pauliSupport, h, axisClifford, SinglePauli.matrix]
    · have hi : i ∈ pauliSupport p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      simpa only [zSubset, if_pos hi] using axisClifford_maps_Z (p i) h
  dsimp only
  change tensorEntries (fun i => axisClifford (p i)) * pauliMatrix 0 (zSubset (pauliSupport p)) *
    (tensorEntries (fun i => axisClifford (p i))).conjTranspose = _
  rw [← tensorEntries_conjTranspose]
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  exact congrArg tensorEntries (funext hc)

/-- Implement an arbitrary Pauli rotation by local Clifford basis
changes, one CNOT parity word and its inverse, and one one-site Z rotation. -/
theorem tensorPauliRotation_via_axisClifford_parity (p : Fin k → SinglePauli)
    (t : Fin k) (ht : t ∈ pauliSupport p) (a : ℝ) :
    let V := tensorEntries fun i => axisClifford (p i)
    let L := ((pauliSupport p).erase t).toList
    let h : ∀ i ∈ L, i ≠ t := fun _ hi =>
      (Finset.mem_erase.mp (Finset.mem_toList.mp hi)).1
    let R := cnotParityWord t L h
    V * (CriticalDepth.BinaryPermutationUnitary.basisPermutation R.symm *
        rotation (pauliMatrix 0 (zSubset {t})) a *
        CriticalDepth.BinaryPermutationUnitary.basisPermutation R) * star V =
      rotation (pauliMatrix 0 p) a := by
  dsimp only
  rw [tensorZRotation_via_cnotParity _ _ ht]
  have hV : (tensorEntries fun i => axisClifford (p i)) *
      star (tensorEntries fun i => axisClifford (p i)) = 1 :=
    (isUnitary_tensorEntries _ (fun i => axisClifford_isUnitary (p i))).2
  simp only [rotation, affine, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, ← tensorAxisClifford_maps_supportZ p, hV]

#print axioms tensorAxisClifford_maps_supportZ
#print axioms tensorPauliRotation_via_axisClifford_parity

end

end CriticalDepth.Manuscript20261114
