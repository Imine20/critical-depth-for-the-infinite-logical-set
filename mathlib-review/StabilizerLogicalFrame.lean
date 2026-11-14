import StabilizerPauliFrameAction
import LogicalPauliVacuum

/-!
# Physical representatives and logical matrices for a selected Pauli frame
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.PauliGroup Matrix
open scoped Kronecker

noncomputable section

variable {n k : ℕ}
variable (C : Code n (fun _ => 2) (2 ^ k) 1)
variable {S : PhysicalStabilizer n}
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
  {v | ∀ U ∈ S, U.val.mulVec v = v})
variable (F : StabilizerPauliFrame S k)

def StabilizerPauliFrame.toLogicalPauliFrame :
    LogicalPauliFrame (Fin k) (Fin (2^k)) where
  X := F.logicalX C
  Z := F.logicalZ C
  xSelf := F.xSelfAdjoint C
  zSelf := F.zSelfAdjoint C
  xSq := F.xSquare C hspace
  zSq := F.zSquare C hspace
  xx := F.logicalXX C hspace
  zz := F.logicalZZ C hspace
  zx_same i := by
    have h := F.logicalXZ C hspace i i
    rw [if_pos rfl, neg_one_smul] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  zx_other i j hij := by
    have h := F.logicalXZ C hspace j i
    rw [if_neg (Ne.symm hij), one_smul] at h
    exact h.symm

theorem pauli_hermitian_phase {a : Fin 4} {p : Fin n → SinglePauli}
    (h : star (pauliMatrix a p) = pauliMatrix a p) :
    pauliMatrix a p = pauliMatrix 0 p ∨ pauliMatrix a p = -(pauliMatrix 0 p) := by
  let z := Complex.I ^ a.val
  let P := pauliMatrix 0 p
  rw [pauliMatrix_eq_phase_smul] at h ⊢
  change star (z • P) = z • P at h
  rw [star_smul, show star P = P from unphased_pauliMatrix_selfAdjoint p] at h
  have e := congrArg (fun A : Operator (QubitBasis n) => A * P) h
  rw [Matrix.smul_mul, Matrix.smul_mul, show P * P = 1 from unphased_pauliMatrix_sq p] at e
  let x : QubitBasis n := fun _ => 0
  have hentry := congrArg (fun A : Operator (QubitBasis n) => A x x) e
  have hphase : star z = z := by
    simpa [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] using hentry
  have hs : z = 1 ∨ z = -1 := by
    fin_cases a
    · left
      norm_num [z]
    · exfalso
      have hbad : star Complex.I = Complex.I := by simpa [z] using hphase
      have he := congrArg Complex.im hbad
      norm_num [show star Complex.I = -Complex.I from Complex.conj_I] at he
    · right
      norm_num [z, pow_succ, Complex.I_mul_I]
    · exfalso
      have hbad : star (-Complex.I) = -Complex.I := by
        simpa [z, pow_succ, Complex.I_mul_I] using hphase
      have he := congrArg Complex.im hbad
      norm_num [show star Complex.I = -Complex.I from Complex.conj_I] at he
  change z • P = P ∨ z • P = -P
  rcases hs with hs | hs
  · exact Or.inl (by simp [hs])
  · exact Or.inr (by simp [hs])

include hspace in
/-- An unphased physical word represents the logical ZZ edge with one of
the two Hermitian signs. The sign comes from the physical Pauli product. -/
theorem StabilizerPauliFrame.exists_zzWord (i j : Fin k) :
    ∃ p : Fin n → SinglePauli,
      (∀ U ∈ S, U.val * pauliMatrix 0 p = pauliMatrix 0 p * U.val) ∧
      let A := F.logicalZ C i * F.logicalZ C j
      (pauliMatrix 0 p * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin 1)))) ∨
      (pauliMatrix 0 p * C.encoding = C.encoding * ((-A) ⊗ₖ (1 : Operator (Fin 1)))) := by
  let P := pauliMatrix 0 (F.zWord i)
  let Q := pauliMatrix 0 (F.zWord j)
  let A := F.logicalZ C i
  let B := F.logicalZ C j
  have hstar : star (P * Q) = P * Q := by
    rw [star_mul, show star P = P from unphased_pauliMatrix_selfAdjoint _,
      show star Q = Q from unphased_pauliMatrix_selfAdjoint _]
    exact (F.zz i j).symm
  have hpq : (P * Q) * C.encoding = C.encoding * ((A*B) ⊗ₖ (1 : Operator (Fin 1))) := by
    rw [Matrix.mul_assoc, show Q * C.encoding = _ from F.zIntertwines C hspace j,
      ← Matrix.mul_assoc P C.encoding, show P * C.encoding = _ from F.zIntertwines C hspace i,
      Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  obtain ⟨a,p,h⟩ := isPauli_mul (show IsPauli P from ⟨0,_,rfl⟩) (show IsPauli Q from ⟨0,_,rfl⟩)
  have hs := pauli_hermitian_phase (h ▸ hstar)
  have hcomm (U : Matrix.unitaryGroup (QubitBasis n) ℂ) (hU : U ∈ S) :
      U.val * (P*Q) = (P*Q) * U.val := by
    calc
      _ = (U.val * P) * Q := by rw [Matrix.mul_assoc]
      _ = (P * U.val) * Q := by rw [show U.val * P = P * U.val from F.zCentral i U hU]
      _ = P * (Q * U.val) := by
        rw [Matrix.mul_assoc, show U.val * Q = Q * U.val from F.zCentral j U hU]
      _ = _ := by rw [Matrix.mul_assoc]
  refine ⟨p,?_ ,?_⟩
  · intro U hU
    have hh := hcomm U hU
    rw [h] at hh
    rcases hs with hs | hs
    · simpa only [hs] using hh
    · rw [hs, Matrix.mul_neg, Matrix.neg_mul] at hh
      exact neg_injective hh
  rcases hs with hs | hs
  · exact Or.inl (by simpa only [h,hs,A,B] using hpq)
  · right
    rw [h,hs,Matrix.neg_mul] at hpq
    have he := congrArg Neg.neg hpq
    rw [neg_neg, ← Matrix.mul_neg] at he
    have hK : -( (A*B) ⊗ₖ (1 : Operator (Fin 1))) =
        (- (A*B)) ⊗ₖ (1 : Operator (Fin 1)) := by
      ext a b
      simp [Matrix.kronecker_apply, Matrix.neg_apply]
    rwa [hK] at he

#print axioms StabilizerPauliFrame.toLogicalPauliFrame
#print axioms StabilizerPauliFrame.exists_zzWord

end

end CriticalDepth.Manuscript20261114
