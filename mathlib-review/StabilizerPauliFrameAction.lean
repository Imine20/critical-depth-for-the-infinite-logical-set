import StabilizerPauliFrame

/-!
# Encoded action of the selected logical Pauli frame
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript Matrix
open scoped Kronecker

noncomputable section

variable {n k : ℕ}
variable (C : Code n (fun _ => 2) (2 ^ k) 1)
variable {S : PhysicalStabilizer n}
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
  {v | ∀ U ∈ S, U.val.mulVec v = v})
variable (F : StabilizerPauliFrame S k)

def StabilizerPauliFrame.logicalX (i : Fin k) : Operator (Fin (2 ^ k)) :=
  subspaceLogicalMatrix C (pauliMatrix 0 (F.xWord i))

def StabilizerPauliFrame.logicalZ (i : Fin k) : Operator (Fin (2 ^ k)) :=
  subspaceLogicalMatrix C (pauliMatrix 0 (F.zWord i))

include hspace in
theorem StabilizerPauliFrame.xIntertwines (i : Fin k) :
    pauliMatrix 0 (F.xWord i) * C.encoding =
      C.encoding * (F.logicalX C i ⊗ₖ (1 : Operator (Fin 1))) := by
  have h := code_preservation_of_stabilizer_commutation C S hspace _ (F.xCentral i)
  rwa [subspaceCompression_eq_kronecker] at h

include hspace in
theorem StabilizerPauliFrame.zIntertwines (i : Fin k) :
    pauliMatrix 0 (F.zWord i) * C.encoding =
      C.encoding * (F.logicalZ C i ⊗ₖ (1 : Operator (Fin 1))) := by
  have h := code_preservation_of_stabilizer_commutation C S hspace _ (F.zCentral i)
  rwa [subspaceCompression_eq_kronecker] at h

theorem StabilizerPauliFrame.xSelfAdjoint (i : Fin k) : star (F.logicalX C i) = F.logicalX C i :=
  subspaceLogicalMatrix_selfAdjoint C _ (unphased_pauliMatrix_selfAdjoint _)

theorem StabilizerPauliFrame.zSelfAdjoint (i : Fin k) : star (F.logicalZ C i) = F.logicalZ C i :=
  subspaceLogicalMatrix_selfAdjoint C _ (unphased_pauliMatrix_selfAdjoint _)

include hspace in
theorem StabilizerPauliFrame.xSquare (i : Fin k) :
    F.logicalX C i * F.logicalX C i = 1 :=
  subspaceLogicalMatrix_sq_of_preserving C _ (unphased_pauliMatrix_sq _)
    (code_preservation_of_stabilizer_commutation C S hspace _ (F.xCentral i))

include hspace in
theorem StabilizerPauliFrame.zSquare (i : Fin k) :
    F.logicalZ C i * F.logicalZ C i = 1 :=
  subspaceLogicalMatrix_sq_of_preserving C _ (unphased_pauliMatrix_sq _)
    (code_preservation_of_stabilizer_commutation C S hspace _ (F.zCentral i))

private theorem compression_transport_commutation
    (P Q : Operator (QubitBasis n)) (A B : Operator (Fin (2^k))) (c : ℂ)
    (hP : P * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin 1))))
    (hQ : Q * C.encoding = C.encoding * (B ⊗ₖ (1 : Operator (Fin 1))))
    (h : P*Q = c • (Q*P)) : A*B = c • (B*A) := by
  let V := C.encoding
  let K (M : Operator (Fin (2^k))) := M ⊗ₖ (1 : Operator (Fin 1))
  have hprod {R T : Operator (QubitBasis n)} {X Y : Operator (Fin (2^k))}
      (hR : R * V = V * K X) (hT : T * V = V * K Y) :
      (R*T) * V = V * K (X*Y) := by
    rw [Matrix.mul_assoc, hT, ← Matrix.mul_assoc R V, hR, Matrix.mul_assoc]
    unfold K
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have he := congrArg (fun M : Operator (QubitBasis n) => V.conjTranspose * (M*V)) h
  rw [hprod hP hQ, Matrix.smul_mul, Matrix.mul_smul, hprod hQ hP,
    ← Matrix.mul_assoc V.conjTranspose V, ← Matrix.mul_assoc V.conjTranspose V,
    show V.conjTranspose * V = 1 from C.isometry, Matrix.one_mul, Matrix.one_mul] at he
  ext i j
  have hentry := congrArg (fun M : Operator (Fin (2^k) × Fin 1) => M (i,0) (j,0)) he
  simpa only [K, Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one, Matrix.smul_apply] using hentry

include hspace in
theorem StabilizerPauliFrame.logicalXX (i j : Fin k) :
    F.logicalX C i * F.logicalX C j = F.logicalX C j * F.logicalX C i := by
  have h := compression_transport_commutation C _ _ _ _ 1
    (F.xIntertwines C hspace i) (F.xIntertwines C hspace j) (by simpa only [one_smul] using F.xx i j)
  simpa only [one_smul] using h

include hspace in
theorem StabilizerPauliFrame.logicalZZ (i j : Fin k) :
    F.logicalZ C i * F.logicalZ C j = F.logicalZ C j * F.logicalZ C i := by
  have h := compression_transport_commutation C _ _ _ _ 1
    (F.zIntertwines C hspace i) (F.zIntertwines C hspace j) (by simpa only [one_smul] using F.zz i j)
  simpa only [one_smul] using h

include hspace in
theorem StabilizerPauliFrame.logicalXZ (i j : Fin k) :
    F.logicalX C i * F.logicalZ C j =
      (if i = j then (-1 : ℂ) else 1) • (F.logicalZ C j * F.logicalX C i) :=
  compression_transport_commutation C _ _ _ _ _
    (F.xIntertwines C hspace i) (F.zIntertwines C hspace j) (F.xz i j)

#print axioms StabilizerPauliFrame.logicalXX
#print axioms StabilizerPauliFrame.logicalZZ
#print axioms StabilizerPauliFrame.logicalXZ

end

end CriticalDepth.Manuscript20261114
