import FaultStabilizerTrace
import PauliGroup

/-!
# Physical stabilizer syndromes and encoded sectors

Stabilizer commutation signs define physical error syndromes. Different
syndromes have orthogonal encoded ranges. Errors sharing a syndrome
differ by a code-preserving Pauli on the encoded input.
-/

namespace CriticalDepth.FaultStabilizerSyndrome

noncomputable section

open Matrix
open CriticalDepth.Manuscript CriticalDepth.PauliGroup

variable {n K : ℕ}

abbrev PhysPauli (n : ℕ) := physicalPauliGroup n

def sectorSign (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (E : PhysPauli n) (T : S) : Bool := by
  classical
  exact decide ((T.val : Operator (QubitBasis n)) * E.val.val = E.val.val * T.val.val)

private theorem pauli_comm_or_anti {A B : Operator (QubitBasis n)}
    (hA : IsPauli A) (hB : IsPauli B) :
    A * B = B * A ∨ A * B = -(B * A) := by
  obtain ⟨a, x, rfl⟩ := hA
  obtain ⟨b, y, rfl⟩ := hB
  exact pauliMatrix_commute_or_anticommute a b x y

private theorem relation_of_sectorSign (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
    (E : PhysPauli n) (T : S) :
    T.val.val * E.val.val =
      (if sectorSign S E T then (1 : ℂ) else -1) • (E.val.val * T.val.val) := by
  classical
  by_cases h : T.val.val * E.val.val = E.val.val * T.val.val
  · simpa [sectorSign, h] using h
  · have h' := (pauli_comm_or_anti (hS T.val T.property) E.property).resolve_left h
    simpa [sectorSign, h] using h'

private theorem branch_eigen
    (C : Code n (fun _ => 2) K 1)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (E : PhysPauli n) (T : S) :
    T.val.val * (E.val.val * C.encoding) =
      (if sectorSign S E T then (1 : ℂ) else -1) • (E.val.val * C.encoding) := by
  rw [← Matrix.mul_assoc, relation_of_sectorSign S hS E T, Matrix.smul_mul,
    Matrix.mul_assoc, encoding_fixed_of_fixedSpace C S hspace T.val T.property]

/-- Different physical commutation signs give orthogonal error isometries. -/
theorem syndrome_orthogonal
    (C : Code n (fun _ => 2) K 1)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (E F : PhysPauli n) (hEF : sectorSign S E ≠ sectorSign S F) :
    (E.val.val * C.encoding).conjTranspose * (F.val.val * C.encoding) = 0 := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, sectorSign S E T ≠ sectorSign S F T := by
    by_contra! h
    exact hEF (funext h)
  let A := E.val.val * C.encoding
  let B := F.val.val * C.encoding
  have hTu : T.val.val.conjTranspose * T.val.val = 1 := T.val.property.1
  have hh : (T.val.val * A).conjTranspose * (T.val.val * B) = A.conjTranspose * B := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc T.val.val.conjTranspose, hTu, Matrix.one_mul]
  rw [show T.val.val * A = _ from branch_eigen C S hS hspace E T,
    show T.val.val * B = _ from branch_eigen C S hS hspace F T,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hh
  have hphase : star (if sectorSign S E T then (1 : ℂ) else -1) *
      (if sectorSign S F T then (1 : ℂ) else -1) = -1 := by
    cases he : sectorSign S E T <;> cases hf : sectorSign S F T <;> simp_all
  rw [hphase] at hh
  change A.conjTranspose * B = 0
  ext i j
  have h := congrArg (fun M : Operator (Fin K × Fin 1) => M i j) hh
  simp only [Matrix.smul_apply, smul_eq_mul, neg_one_mul, Matrix.zero_apply] at h ⊢
  linear_combination (-1 / 2 : ℂ) * h

/-- Equal signs imply that the difference between the two physical Paulis
commutes with every stabilizer. -/
theorem same_syndrome_relative_commutes
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
    (E F : PhysPauli n) (hEF : sectorSign S E = sectorSign S F) :
    ∀ T ∈ S, (T : Operator (QubitBasis n)) * (E.val.val.conjTranspose * F.val.val) =
      (E.val.val.conjTranspose * F.val.val) * (T : Operator (QubitBasis n)) := by
  intro T hT
  let U := (T : Operator (QubitBasis n))
  let A := E.val.val
  let B := F.val.val
  have hA : A * A.conjTranspose = 1 := E.val.property.2
  let z : ℂ := if sectorSign S E ⟨T, hT⟩ then 1 else -1
  have hz : z * z = 1 := by
    unfold z
    split <;> norm_num
  have hUA : U * A = z • (A * U) := relation_of_sectorSign S hS E ⟨T, hT⟩
  have hUB : U * B = z • (B * U) := by
    have h := relation_of_sectorSign S hS F ⟨T, hT⟩
    rwa [← hEF] at h
  have hAU : U * A.conjTranspose = z • (A.conjTranspose * U) := by
    have hU := congrArg (fun M => A.conjTranspose * M * A.conjTranspose) hUA
    have hA' : A.conjTranspose * A = 1 := E.val.property.1
    have hh : A.conjTranspose * U = z • (U * A.conjTranspose) := by
      simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hA,
        ← Matrix.mul_assoc A.conjTranspose A U, hA', Matrix.one_mul, Matrix.mul_one] using hU
    calc
      _ = (z * z) • (U * A.conjTranspose) := by rw [hz, one_smul]
      _ = z • (A.conjTranspose * U) := by rw [hh, smul_smul]
  change U * (A.conjTranspose * B) = _
  rw [← Matrix.mul_assoc, hAU, Matrix.smul_mul, Matrix.mul_assoc, hUB,
    Matrix.mul_smul, smul_smul, hz, one_smul, ← Matrix.mul_assoc]

/-- The relative Pauli in a syndrome sector acts by a logical unitary. -/
theorem same_syndrome_relative_logical
    (C : Code n (fun _ => 2) K 1)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (E F : PhysPauli n) (hEF : sectorSign S E = sectorSign S F) :
    ∃ W : Operator (Fin K × Fin 1), W.conjTranspose * W = 1 ∧
      F.val.val * C.encoding = (E.val.val * C.encoding) * W := by
  let P := E.val.val.conjTranspose * F.val.val
  let W := C.encoding.conjTranspose * P * C.encoding
  have hpres : P * C.encoding = C.encoding * W :=
    code_preservation_of_stabilizer_commutation C S hspace P
      (same_syndrome_relative_commutes S hS E F hEF)
  have hE : E.val.val * E.val.val.conjTranspose = 1 := E.val.property.2
  have hF : F.val.val.conjTranspose * F.val.val = 1 := F.val.property.1
  have hU : P.conjTranspose * P = 1 := by
    change (E.val.val.conjTranspose * F.val.val).conjTranspose *
      (E.val.val.conjTranspose * F.val.val) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc E.val.val E.val.val.conjTranspose F.val.val,
      hE, Matrix.one_mul, hF]
  have hIso : (C.encoding * W).conjTranspose * (C.encoding * W) = 1 := by
    rw [← hpres, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc P.conjTranspose P, hU, Matrix.one_mul, C.isometry]
  refine ⟨W, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc C.encoding.conjTranspose C.encoding W, C.isometry, Matrix.one_mul] using hIso
  · have hh := congrArg (fun A => E.val.val * A) hpres
    change E.val.val * ((E.val.val.conjTranspose * F.val.val) * C.encoding) =
      E.val.val * (C.encoding * W) at hh
    rw [← Matrix.mul_assoc E.val.val (E.val.val.conjTranspose * F.val.val),
      ← Matrix.mul_assoc E.val.val E.val.val.conjTranspose, hE,
      Matrix.one_mul, ← Matrix.mul_assoc] at hh
    exact hh

#print axioms syndrome_orthogonal
#print axioms same_syndrome_relative_commutes
#print axioms same_syndrome_relative_logical

end
end CriticalDepth.FaultStabilizerSyndrome
