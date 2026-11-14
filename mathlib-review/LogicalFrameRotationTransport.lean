import ConnectedPauliFrameSynthesis

/-!
# Signed logical representatives after a computational basis change
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix

noncomputable section

variable {n k : ℕ} {ι : Type*}
variable {C : Code n (fun _ => 2) (2 ^ k) 1}

/-- Conjugate computational Pauli products into the chosen logical basis. -/
def logicalFrameAction (e : QubitBasis k ≃ Fin (2 ^ k))
    (U : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ) :
    Matrix.unitaryGroup (QubitBasis k) ℂ ≃* Matrix.unitaryGroup (Fin (2 ^ k)) ℂ :=
  (unitaryBasisReindex e).trans (MulAut.conj U)

/-- The same action on projective logical classes. -/
def logicalFrameProjective (e : QubitBasis k ≃ Fin (2 ^ k))
    (U : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ) :
    PU (QubitBasis k) ≃* PU (Fin (2 ^ k)) :=
  (projectiveBasisReindex e).trans (MulAut.conj (projectiveMk (Fin (2 ^ k)) U))

theorem logicalFrameProjective_mk (e : QubitBasis k ≃ Fin (2 ^ k))
    (U : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ)
    (V : Matrix.unitaryGroup (QubitBasis k) ℂ) :
    logicalFrameProjective e U (projectiveMk (QubitBasis k) V) =
      projectiveMk (Fin (2 ^ k)) (logicalFrameAction e U V) := by
  change (MulAut.conj (projectiveMk (Fin (2 ^ k)) U))
    (projectiveBasisReindex e (projectiveMk (QubitBasis k) V)) = _
  rw [projectiveBasisReindex_mk, MulAut.conj_apply]
  change projectiveMk (Fin (2 ^ k)) U *
    projectiveMk (Fin (2 ^ k)) (unitaryBasisReindex e V) *
    (projectiveMk (Fin (2 ^ k)) U)⁻¹ =
      projectiveMk (Fin (2 ^ k)) (U * unitaryBasisReindex e V * U⁻¹)
  rw [map_mul, map_mul, map_inv]

/-- A signed physical representative supplies the corresponding
computational-axis projective rotation at angle `t` or `-t`. -/
theorem PauliRotationFamily.logicalFrameProjective_rotation_mem_alphabet
    (F : PauliRotationFamily C ι) (e : QubitBasis k ≃ Fin (2 ^ k))
    (U : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ) (w : Fin k → SinglePauli)
    (a : ι)
    (h : let Q : Operator (Fin (2 ^ k)) :=
        (Unitary.conjStarAlgAut ℂ (Operator (Fin (2 ^ k))) U)
          (Matrix.reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 w))
      F.logical a = Q ∨ F.logical a = -Q)
    (t : ℝ) :
    logicalFrameProjective e U (projectiveMk (QubitBasis k) (tensorPauliRotation w t)) ∈
      F.alphabet := by
  let R := Matrix.reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 w)
  let Q := Unitary.conjStarAlgAut ℂ (Operator (Fin (2 ^ k))) U R
  have hAct : (logicalFrameAction e U (tensorPauliRotation w t)).val = rotation Q t := by
    change Unitary.conjStarAlgAut ℂ (Operator (Fin (2 ^ k))) U
      (Matrix.reindexAlgEquiv ℂ ℂ e (rotation (pauliMatrix 0 w) t)) = _
    simp only [rotation, affine, map_add, map_smul, map_one, Q, R]
  rw [logicalFrameProjective_mk]
  change F.logical a = Q ∨ F.logical a = -Q at h
  rcases h with h | h
  · refine ⟨a, t, ?_⟩
    apply congrArg (projectiveMk (Fin (2 ^ k)))
    apply Subtype.ext
    change rotation (F.logical a) t = (logicalFrameAction e U (tensorPauliRotation w t)).val
    rw [h, hAct]
  · refine ⟨a, -t, ?_⟩
    apply congrArg (projectiveMk (Fin (2 ^ k)))
    apply Subtype.ext
    change rotation (F.logical a) (-t) = (logicalFrameAction e U (tensorPauliRotation w t)).val
    rw [h, hAct]
    simp [rotation, affine, Real.cos_neg, Real.sin_neg, smul_neg]

#print axioms PauliRotationFamily.logicalFrameProjective_rotation_mem_alphabet

end

end CriticalDepth.Manuscript20261114
