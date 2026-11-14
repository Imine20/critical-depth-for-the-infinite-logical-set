import SupplementSynthesis
import TensorPauliConnectedFrame
import MatrixUnitaryConnected
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# The exact generator depth of a connected logical Pauli frame
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix Relation
open scoped BigOperators

noncomputable section

section Reindex

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable (e : α ≃ β)

private theorem reindexAlgEquiv_star (A : Operator α) :
    reindexAlgEquiv ℂ ℂ e (star A) = star (reindexAlgEquiv ℂ ℂ e A) := by
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_reindex]

private theorem isUnitary_reindexAlgEquiv (A : Operator α) (hA : IsUnitary A) :
    IsUnitary (reindexAlgEquiv ℂ ℂ e A) := by
  constructor
  · rw [← reindexAlgEquiv_star e, ← map_mul, hA.1, map_one]
  · rw [← reindexAlgEquiv_star e, ← map_mul, hA.2, map_one]

/-- Reindexing the computational basis transports the unitary matrix group. -/
def unitaryBasisReindex : Matrix.unitaryGroup α ℂ ≃* Matrix.unitaryGroup β ℂ where
  toFun U := ⟨reindexAlgEquiv ℂ ℂ e U.val, isUnitary_reindexAlgEquiv e _ U.property⟩
  invFun U := ⟨reindexAlgEquiv ℂ ℂ e.symm U.val, isUnitary_reindexAlgEquiv e.symm _ U.property⟩
  left_inv U := by apply Subtype.ext; exact (reindexAlgEquiv ℂ ℂ e).symm_apply_apply U.val
  right_inv U := by apply Subtype.ext; exact (reindexAlgEquiv ℂ ℂ e).apply_symm_apply U.val
  map_mul' U V := by apply Subtype.ext; exact map_mul (reindexAlgEquiv ℂ ℂ e) U.val V.val

private theorem unitaryBasisReindex_phase (z : unitary ℂ) :
    unitaryBasisReindex e (scalarPhaseHom α z) = scalarPhaseHom β z := by
  apply Subtype.ext
  change reindexAlgEquiv ℂ ℂ e ((scalarPhaseHom α z).val) = (scalarPhaseHom β z).val
  rw [scalarPhaseHom_val, scalarPhaseHom_val, map_smul, map_one]

private theorem unitaryBasisReindex_maps_scalar :
    (scalarPhaseSubgroup α).map (unitaryBasisReindex e) = scalarPhaseSubgroup β := by
  ext W
  constructor
  · rintro ⟨U, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (unitaryBasisReindex_phase e z).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨scalarPhaseHom α z, ⟨z, rfl⟩, unitaryBasisReindex_phase e z⟩

/-- Reindexing preserves the projective phase equivalence. -/
def projectiveBasisReindex : PU α ≃* PU β :=
  QuotientGroup.congr (scalarPhaseSubgroup α) (scalarPhaseSubgroup β)
    (unitaryBasisReindex e) (unitaryBasisReindex_maps_scalar e)

theorem projectiveBasisReindex_mk (U : Matrix.unitaryGroup α ℂ) :
    projectiveBasisReindex e (projectiveMk α U) =
      projectiveMk β (unitaryBasisReindex e U) := rfl

private theorem unitaryBasisReindex_rotation (P : Operator α)
    (hP : star P = P) (hSq : P * P = 1) (t : ℝ)
    (Q : Operator β) (hQ : star Q = Q) (hQSq : Q * Q = 1)
    (hPQ : reindexAlgEquiv ℂ ℂ e P = Q) :
    unitaryBasisReindex e (unitaryRotation P hP hSq t) = unitaryRotation Q hQ hQSq t := by
  apply Subtype.ext
  change reindexAlgEquiv ℂ ℂ e (rotation P t) = rotation Q t
  unfold rotation affine
  rw [map_add, map_smul, map_smul, map_one, hPQ]

end Reindex

private theorem unitary_conjugation_rotation {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (P : Operator α)
    (hp : star P = P) (hps : P * P = 1) (Q : Operator α)
    (hq : star Q = Q) (hqs : Q * Q = 1)
    (hPQ : Unitary.conjStarAlgAut ℂ (Operator α) U P = Q) (t : ℝ) :
    U * unitaryRotation P hp hps t * U⁻¹ = unitaryRotation Q hq hqs t := by
  apply Subtype.ext
  change Unitary.conjStarAlgAut ℂ (Operator α) U (rotation P t) = rotation Q t
  unfold rotation affine
  rw [map_add, map_smul, map_smul, map_one, hPQ]

variable {n k : ℕ}

/-- The maximum-weight physical synthesis theorem applies to the connected
Pauli frame in any chosen logical computational basis. Each required
direction is represented separately in the indexed family. -/
theorem exact_generator_depth_bounds_of_connectedPauliFrame {d : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hk : 1 ≤ k) (hd : 2 ≤ d) (q : ℕ) (hq : 2 ≤ q)
    (hstab : IsStabilizer C) (hdist : HasActualDistance C d)
    (F : PauliRotationFamily C ι) (hF : ∀ i, ¬ IsScalar (F.logical i))
    (e : QubitBasis k ≃ Fin (2 ^ k))
    (U : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ)
    (E : Fin k → Fin k → Prop) (hConnected : ∀ i j, ReflTransGen E i j)
    (hX : ∀ i, ∃ a,
      let Q := Unitary.conjStarAlgAut ℂ _ U (reindexAlgEquiv ℂ ℂ e
        (pauliMatrix 0 (singleSitePauli i .X)))
      F.logical a = Q ∨ F.logical a = -Q)
    (hZ : ∀ i, ∃ a,
      let Q := Unitary.conjStarAlgAut ℂ _ U (reindexAlgEquiv ℂ ℂ e
        (pauliMatrix 0 (singleSitePauli i .Z)))
      F.logical a = Q ∨ F.logical a = -Q)
    (hZZ : ∀ i j, E i j → i ≠ j → ∃ a,
      let Q := Unitary.conjStarAlgAut ℂ _ U (reindexAlgEquiv ℂ ℂ e
        (pauliMatrix 0 (pairPauli i j .Z .Z)))
      F.logical a = Q ∨ F.logical a = -Q) :
    (Arithmetic.criticalDepth q d : ℕ∞) ≤ nativeExactDepth C.encoding q ∧
      nativeExactDepth C.encoding q ≤ (Arithmetic.criticalDepth q F.maxWeight : ℕ∞) ∧
      Arithmetic.criticalDepth q F.maxWeight ≤ Arithmetic.criticalDepth q n := by
  let G := Subgroup.closure F.alphabet
  let P := (projectiveBasisReindex e).trans (MulAut.conj (projectiveMk (Fin (2 ^ k)) U))
  let H := G.comap P.toMonoidHom
  have hAxis (w : Fin k → SinglePauli)
      (ha : ∃ a : ι,
        let Q := Unitary.conjStarAlgAut ℂ (Operator (Fin (2 ^ k))) U
          (reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 w))
        F.logical a = Q ∨ F.logical a = -Q) :
      HasTensorPauliRotations H w := by
    obtain ⟨a, ha⟩ := ha
    intro t
    let R := reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 w)
    let Q := Unitary.conjStarAlgAut ℂ (Operator (Fin (2 ^ k))) U R
    have hr := isUnitary_reindexAlgEquiv e _ (unphased_pauliMatrix_isUnitary w)
    have hR : star R = R := by
      change star (reindexAlgEquiv ℂ ℂ e _) = _
      rw [← reindexAlgEquiv_star, show star (pauliMatrix 0 w) = pauliMatrix 0 w from
        unphased_pauliMatrix_selfAdjoint w]
    have hRS : R * R = 1 := by
      have h := hr.1
      change star R * R = 1 at h
      rwa [hR] at h
    have hQ : star Q = Q := by
      change star (Unitary.conjStarAlgAut ℂ _ U R) = _
      rw [← map_star, hR]
    have hQS : Q * Q = 1 := by
      change Unitary.conjStarAlgAut ℂ _ U R * Unitary.conjStarAlgAut ℂ _ U R = 1
      rw [← map_mul, hRS, map_one]
    change (MulAut.conj (projectiveMk (Fin (2 ^ k)) U))
      (projectiveBasisReindex e (projectiveMk (QubitBasis k) (tensorPauliRotation w t))) ∈ G
    rw [projectiveBasisReindex_mk, tensorPauliRotation,
      unitaryBasisReindex_rotation e _ _ _ t R hR hRS rfl, MulAut.conj_apply,
      ← map_inv, ← map_mul, ← map_mul,
      unitary_conjugation_rotation U R hR hRS Q hQ hQS rfl]
    apply Subgroup.subset_closure
    change F.logical a = Q ∨ F.logical a = -Q at ha
    rcases ha with h | h
    · refine ⟨a,t,?_⟩
      apply congrArg (projectiveMk (Fin (2 ^ k)))
      apply Subtype.ext
      change rotation (F.logical a) t = rotation Q t
      rw [h]
    · refine ⟨a,-t,?_⟩
      apply congrArg (projectiveMk (Fin (2 ^ k)))
      apply Subtype.ext
      change rotation (F.logical a) (-t) = rotation Q t
      rw [h]
      simp [rotation, affine, Real.cos_neg, Real.sin_neg, smul_neg]
  have hAll := hasAllTensorPauliRotations_of_connectedFrame H E hConnected
    (fun i => hAxis _ (hX i)) (fun i => hAxis _ (hZ i))
    (fun i j hij hne => hAxis _ (hZZ i j hij hne))
  have hTop : H = ⊤ := projectiveUnitary_eq_top_of_open H
    (isOpen_of_contains_tensorPauliRotations H hAll)
  have hGen : G = ⊤ := by
    apply top_unique
    intro U _
    obtain ⟨V, rfl⟩ := P.surjective U
    change V ∈ H
    rw [hTop]
    exact Subgroup.mem_top V
  exact exact_generator_depth_bounds_of_logical_generation C hk hd q hq hstab hdist F hF hGen

#print axioms projectiveBasisReindex
#print axioms exact_generator_depth_bounds_of_connectedPauliFrame

end

end CriticalDepth.Manuscript20261114
