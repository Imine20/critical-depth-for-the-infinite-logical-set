import CriticalDepth.ManuscriptStatements
import CriticalDepth.Compression

/-!
# The depth-zero specialization of the manuscript's first theorem

This module proves a special case of the original concrete logical-image
definition. It does not assume finite image, finite cells, infinitesimal
rigidity, or a circuit-synthesis principle. At depth zero, the physical
circuit evaluates to the identity. The encoding isometry then forces the
logical factor to be a scalar unitary.
-/

noncomputable section

namespace CriticalDepth

open Matrix
open scoped Kronecker

theorem projectivelyEquivalent_one_of_unitary_scalar
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {W : Operator ι} (hW : IsUnitary W) (hscalar : IsScalar W) :
    ProjectivelyEquivalent W 1 := by
  classical
  obtain ⟨z, hz⟩ := hscalar
  refine ⟨z, ?_, hz⟩
  have hunit := hW.1
  rw [hz] at hunit
  have hnorm : (star z * z) • (1 : Operator ι) = 1 := by
    simpa [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm] using hunit
  let i : ι := Classical.choice inferInstance
  have hdiag := congrArg (fun A : Operator ι => A i i) hnorm
  simpa using hdiag

namespace Manuscript

@[simp] theorem circuitEval_depth_zero
    {n q : ℕ} {dim : Fin n → ℕ} (c : Circuit n dim q 0) :
    circuitEval c = 1 := by
  simp [circuitEval]

theorem identity_implements_projective_identity
    {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g)
    (W : Operator (Fin K)) (himpl : Implements C 1 W) :
    ProjectivelyEquivalent W 1 := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin g) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hW, Z, hZ, hencoded⟩ := himpl
  have hencoded' : C.encoding = C.encoding * (W ⊗ₖ Z) := by
    simpa only [Matrix.one_mul] using hencoded
  have hT : W ⊗ₖ Z = 1 := by
    calc
      W ⊗ₖ Z = (C.encoding.conjTranspose * C.encoding) * (W ⊗ₖ Z) := by
        rw [C.isometry]
        simp
      _ = C.encoding.conjTranspose * (C.encoding * (W ⊗ₖ Z)) := by
        rw [Matrix.mul_assoc]
      _ = C.encoding.conjTranspose * C.encoding := by rw [← hencoded']
      _ = 1 := C.isometry
  have hZright : Z * Z.conjTranspose = 1 := hZ.2
  have hTensor : W ⊗ₖ (1 : Operator (Fin g)) =
      (1 : Operator (Fin K)) ⊗ₖ Z.conjTranspose := by
    calc
      W ⊗ₖ (1 : Operator (Fin g)) =
          (W * (1 : Operator (Fin K))) ⊗ₖ (Z * Z.conjTranspose) := by
            rw [mul_one, hZright]
      _ = (W ⊗ₖ Z) * ((1 : Operator (Fin K)) ⊗ₖ Z.conjTranspose) :=
        Matrix.mul_kronecker_mul W (1 : Operator (Fin K)) Z Z.conjTranspose
      _ = (1 : Operator (Fin K)) ⊗ₖ Z.conjTranspose := by rw [hT, one_mul]
  have hzero : (1 : Operator (Fin K)) ⊗ₖ (0 : Operator (Fin g)) = 0 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [Matrix.kronecker_apply]
  have hscalar : IsScalar W := by
    apply scalarity_of_tensor_generator W (0 : Operator (Fin g)) Z.conjTranspose
    rw [hzero, add_zero]
    exact hTensor
  exact projectivelyEquivalent_one_of_unitary_scalar hW hscalar

/--
Depth zero is an actual proved specialization of Theorem 1's logical-image
claim. No distance assumption is needed for this specialization.
-/
theorem depth_zero_logicalImage_finite
    {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g) (q : ℕ) :
    (logicalImage C q 0).Finite := by
  classical
  refine (Set.finite_singleton (projectiveClass (1 : Operator (Fin K)))).subset ?_
  intro a ha
  obtain ⟨c, W, himpl, hclass⟩ := ha
  have himpl0 : Implements C 1 W := by
    simpa only [circuitEval_depth_zero] using himpl
  have hp : ProjectivelyEquivalent W 1 :=
    identity_implements_projective_identity C hK hg W himpl0
  have hq : projectiveClass W = projectiveClass (1 : Operator (Fin K)) :=
    Quotient.sound hp
  exact Set.mem_singleton_iff.mpr (hclass.symm.trans hq)

/-- A real call at the manuscript's original distance-assumption scope. -/
example (n K g d q : ℕ) (dim : Fin n → ℕ)
    (_hn : 1 ≤ n) (hK : 2 ≤ K) (hg : 1 ≤ g) (_hd : 2 ≤ d)
    (C : Code n dim K g) (_hdetect : DetectsBelow C d) :
    (logicalImage C q 0).Finite := by
  exact depth_zero_logicalImage_finite C hK hg q

#print axioms CriticalDepth.projectivelyEquivalent_one_of_unitary_scalar
#print axioms CriticalDepth.Manuscript.identity_implements_projective_identity
#print axioms CriticalDepth.Manuscript.depth_zero_logicalImage_finite

end Manuscript
end CriticalDepth
