import Q37CanonicalEncoding
import Q37ActualDistance
import BinaryPermutationUnitary

/-!
# Actual distance and stabilizer of the ordered Q37 encoding

The physical code space is the same CSS coset space. Its two different
logical index types are related by a permutation matrix between the
bases, so compression into scalars and the full encoded range agree.
-/

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.BinaryPermutationUnitary CriticalDepth.FaultShorSaturation
open scoped Kronecker BigOperators

noncomputable section

private abbrev OldQ37Index := Fin (2 ^ cssLogicalQubits q37XChecks q37ZChecks) × Fin 1
private abbrev OrderedQ37Index := Fin 2 × Fin 1

private def q37IndexEquiv : OrderedQ37Index ≃ OldQ37Index :=
  (logicalCosetEquiv q37XChecks q37ZChecks q37LogicalX_in_dual
    q37LogicalX_not_check q37LogicalQubits).trans
    (cssLogicalEquiv q37XChecks q37ZChecks).symm

private def q37ColumnChange : Matrix OldQ37Index OrderedQ37Index ℂ :=
  fun a b => if a = q37IndexEquiv b then 1 else 0

private theorem q37ColumnChange_left :
    q37ColumnChange.conjTranspose * q37ColumnChange = 1 := by
  classical
  ext a b
  change (∑ k : OldQ37Index, star (if k = q37IndexEquiv a then (1 : ℂ) else 0) *
      (if k = q37IndexEquiv b then 1 else 0)) = _
  by_cases h : a = b
  · subst b
    simp [apply_ite star, ite_mul, Matrix.one_apply_eq, Finset.sum_ite_eq']
  · have hneq : q37IndexEquiv a ≠ q37IndexEquiv b := fun h' => h (q37IndexEquiv.injective h')
    have hp (k : OldQ37Index) : star (if k = q37IndexEquiv a then (1 : ℂ) else 0) *
        (if k = q37IndexEquiv b then 1 else 0) = 0 := by
      by_cases hk : k = q37IndexEquiv a
      · subst k
        simp [hneq]
      · simp [hk]
    simp only [hp, Finset.sum_const_zero]
    exact (Matrix.one_apply_ne h).symm

private theorem q37ColumnChange_right :
    q37ColumnChange * q37ColumnChange.conjTranspose = 1 := by
  classical
  ext a b
  obtain ⟨u,rfl⟩ := q37IndexEquiv.surjective a
  obtain ⟨v,rfl⟩ := q37IndexEquiv.surjective b
  change (∑ k : OrderedQ37Index, (if q37IndexEquiv u = q37IndexEquiv k then (1 : ℂ) else 0) *
      star (if q37IndexEquiv v = q37IndexEquiv k then 1 else 0)) = _
  by_cases h : u = v
  · subst v
    simp [apply_ite star, ite_mul, Matrix.one_apply_eq, Finset.sum_ite_eq, q37IndexEquiv.injective.eq_iff]
  · have hneq : q37IndexEquiv u ≠ q37IndexEquiv v := fun h' => h (q37IndexEquiv.injective h')
    have hp (k : OrderedQ37Index) : (if q37IndexEquiv u = q37IndexEquiv k then (1 : ℂ) else 0) *
        star (if q37IndexEquiv v = q37IndexEquiv k then 1 else 0) = 0 := by
      by_cases hk : k = u
      · subst k
        simp [Ne.symm hneq]
      · have h' : q37IndexEquiv u ≠ q37IndexEquiv k := fun hh => hk (q37IndexEquiv.injective hh).symm
        simp [h']
    simp only [hp, Finset.sum_const_zero]
    exact (Matrix.one_apply_ne hneq).symm

set_option maxRecDepth 4096 in
private theorem q37Canonical_eq_columnChange :
    q37CanonicalCode.encoding = q37Code.encoding * q37ColumnChange := by
  classical
  ext x b
  change orderedCSSEncoding q37XChecks q37ZChecks q37LogicalX_in_dual x b =
    (cssEncoding q37XChecks q37ZChecks * q37ColumnChange) x b
  rw [Matrix.mul_apply]
  simp only [q37ColumnChange, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change cssCosetEncoding q37XChecks q37ZChecks (binaryWordEquiv 37 x)
      (logicalCoset q37XChecks q37ZChecks q37LogicalX_in_dual b) =
    cssCosetEncoding q37XChecks q37ZChecks (binaryWordEquiv 37 x)
      (cssLogicalEquiv q37XChecks q37ZChecks (q37IndexEquiv b))
  unfold q37IndexEquiv
  rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

private theorem q37_original_eq_columnChange :
    q37Code.encoding = q37CanonicalCode.encoding * q37ColumnChange.conjTranspose := by
  rw [q37Canonical_eq_columnChange, Matrix.mul_assoc, q37ColumnChange_right, Matrix.mul_one]

private theorem scalar_eq_kronecker_finOne {K : ℕ} (z : ℂ) (G : Operator (Fin 1)) (hG : G 0 0 = z) :
    (1 : Operator (Fin K)) ⊗ₖ G = z • (1 : Operator (Fin K × Fin 1)) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a
  subst b
  simp [Matrix.kronecker_apply, Matrix.one_apply, hG, mul_comm]

private theorem gaugeOnly_iff_scalar {K : ℕ} (C : Code 37 (fun _ => 2) K 1)
    (O : Operator (QubitBasis 37)) :
    GaugeOnly C O ↔ IsScalar (C.encoding.conjTranspose * O * C.encoding) := by
  constructor
  · rintro ⟨G,hG⟩
    exact ⟨G 0 0, hG.trans (scalar_eq_kronecker_finOne _ _ rfl)⟩
  · rintro ⟨z,hz⟩
    let G : Operator (Fin 1) := fun _ _ => z
    have hG : G 0 0 = z := rfl
    exact ⟨G, hz.trans (scalar_eq_kronecker_finOne z G hG).symm⟩

private theorem scalarCompression_columnChange {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (V : Matrix (QubitBasis 37) α ℂ) (T : Matrix α β ℂ)
    (hT : T.conjTranspose * T = 1) (O : Operator (QubitBasis 37))
    (h : IsScalar (V.conjTranspose * O * V)) :
    IsScalar ((V * T).conjTranspose * O * (V * T)) := by
  obtain ⟨z,hz⟩ := h
  refine ⟨z,?_⟩
  calc
    (V * T).conjTranspose * O * (V * T) =
        T.conjTranspose * (V.conjTranspose * O * V) * T := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hT]

theorem q37Canonical_gaugeOnly_iff (O : Operator (QubitBasis 37)) :
    GaugeOnly q37CanonicalCode O ↔ GaugeOnly q37Code O := by
  rw [gaugeOnly_iff_scalar, gaugeOnly_iff_scalar]
  constructor
  · intro h
    rw [q37_original_eq_columnChange]
    apply scalarCompression_columnChange _ _ _ _ h
    rw [Matrix.conjTranspose_conjTranspose, q37ColumnChange_right]
  · intro h
    rw [q37Canonical_eq_columnChange]
    exact scalarCompression_columnChange _ _ q37ColumnChange_left _ h

theorem q37CanonicalCode_actualDistance : HasActualDistance q37CanonicalCode 7 := by
  obtain ⟨hdet,S,hS,O,hO,hbad⟩ := q37Code_actualDistance
  refine ⟨?_,S,hS,O,hO,?_⟩
  · intro T hT P hP
    exact (q37Canonical_gaugeOnly_iff P).mpr (hdet T hT P hP)
  · intro h
    exact hbad ((q37Canonical_gaugeOnly_iff O).mp h)

set_option maxRecDepth 4096 in
theorem q37CanonicalCode_isStabilizer : IsStabilizer (k := 1) q37CanonicalCode := by
  let T := q37ColumnChange
  have hSpace := cssEncoding_range_eq_stabilizer q37XChecks q37ZChecks q37ChecksCompatible
  refine ⟨cssStabilizer q37XChecks q37ZChecks,
    fun _ hU => cssStabilizer_le_physicalPauliGroup q37XChecks q37ZChecks hU, ?_⟩
  refine Eq.trans ?_ hSpace
  change Set.range (fun v => q37CanonicalCode.encoding.mulVec v) =
    Set.range (fun v => (cssEncoding q37XChecks q37ZChecks).mulVec v)
  change Set.range (fun v => q37CanonicalCode.encoding.mulVec v) =
    Set.range (fun v => q37Code.encoding.mulVec v)
  ext f
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨T.mulVec w, ?_⟩
    change q37Code.encoding.mulVec (T.mulVec w) = f
    rw [Matrix.mulVec_mulVec]
    change q37CanonicalCode.encoding.mulVec w = f at hw
    rw [q37Canonical_eq_columnChange] at hw
    exact hw
  · rintro ⟨w,hw⟩
    refine ⟨T.conjTranspose.mulVec w, ?_⟩
    change q37CanonicalCode.encoding.mulVec (T.conjTranspose.mulVec w) = f
    rw [Matrix.mulVec_mulVec]
    change q37Code.encoding.mulVec w = f at hw
    rw [q37_original_eq_columnChange] at hw
    exact hw

#print axioms q37CanonicalCode_actualDistance
#print axioms q37CanonicalCode_isStabilizer

end

end CriticalDepth.Q37BinaryData
