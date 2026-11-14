import ShorPhysicalZChecks

/-!
# The rectangular Shor encoding is the fixed space of a physical Pauli subgroup

The subgroup consists of products of the even-row X checks and the
two-full-row Z checks. Membership in the physical Pauli group follows
from that group's multiplicative closure.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.PauliGroup
open CriticalDepth.BinaryPermutationUnitary

variable {rows columns : ℕ}

private noncomputable def unphasedPauliUnitary {n : ℕ} (p : Fin n → SinglePauli) :
    Matrix.unitaryGroup (QubitBasis n) ℂ :=
  ⟨pauliMatrix 0 p, (isUnitary_iff_mem_unitaryGroup (QubitBasis n) _).mp
    (unphased_pauliMatrix_isUnitary p)⟩

private def physicalShorGenerators (rows columns : ℕ) :
    Set (Matrix.unitaryGroup (QubitBasis (rows * columns)) ℂ) :=
  {U | (∃ a : Mask rows columns, xChecks a ∧ U = unphasedPauliUnitary (physicalXWord a)) ∨
    ∃ i j : Fin rows, U = unphasedPauliUnitary (physicalZWord (rowPairZMask i j))}

/-- The generated subgroup of the physical Pauli group on the rectangle. -/
noncomputable def physicalShorStabilizer (rows columns : ℕ) :
    Subgroup (Matrix.unitaryGroup (QubitBasis (rows * columns)) ℂ) :=
  Subgroup.closure (physicalShorGenerators rows columns)

private theorem physicalShorStabilizer_le_Pauli :
    physicalShorStabilizer rows columns ≤ physicalPauliGroup (rows * columns) := by
  apply (Subgroup.closure_le (physicalPauliGroup (rows * columns))).mpr
  intro U hU
  change IsPauli U.val
  rcases hU with ⟨a, _, rfl⟩ | ⟨i, j, rfl⟩
  · exact ⟨0, physicalXWord a, rfl⟩
  · exact ⟨0, physicalZWord (rowPairZMask i j), rfl⟩

private def fixesVectorGroup {n : ℕ} (v : QubitBasis n → ℂ) :
    Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ) where
  carrier := {U | U.val.mulVec v = v}
  one_mem' := Matrix.one_mulVec _
  mul_mem' := by
    intro U W hU hW
    change U.val.mulVec v = v at hU
    change W.val.mulVec v = v at hW
    change (U.val * W.val).mulVec v = v
    rw [← Matrix.mulVec_mulVec, hW, hU]
  inv_mem' := by
    intro U hU
    change U.val.mulVec v = v at hU
    have hunit : star U.val * U.val = 1 :=
      ((isUnitary_iff_mem_unitaryGroup (QubitBasis n) U.val).mpr U.property).1
    change (star U.val).mulVec v = v
    calc
      (star U.val).mulVec v = (star U.val).mulVec (U.val.mulVec v) := by rw [hU]
      _ = v := by rw [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]

private theorem fixed_physicalShorStabilizer_iff
    (v : Mask rows columns → ℂ) :
    (∀ U ∈ physicalShorStabilizer rows columns,
        U.val.mulVec (v ∘ shorBasisEquiv rows columns) = v ∘ shorBasisEquiv rows columns) ↔
      (∀ a : Mask rows columns, xChecks a →
        (basisPermutation (translate a)).mulVec v = v) ∧
      ∀ i j : Fin rows, (shorZPairCheck i j).mulVec v = v := by
  let e := shorBasisEquiv rows columns
  constructor
  · intro h
    constructor
    · intro a ha
      funext x
      obtain ⟨y, rfl⟩ := e.surjective x
      have hu := congrFun (h (unphasedPauliUnitary (physicalXWord a))
        (Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩))) y
      exact (physicalXWord_mulVec a v y).symm.trans hu
    · intro i j
      funext x
      obtain ⟨y, rfl⟩ := e.surjective x
      have hu := congrFun (h (unphasedPauliUnitary (physicalZWord (rowPairZMask i j)))
        (Subgroup.subset_closure (Or.inr ⟨i, j, rfl⟩))) y
      exact (physicalZPair_mulVec i j v y).symm.trans hu
  · rintro ⟨hX, hZ⟩
    apply (show physicalShorStabilizer rows columns ≤ fixesVectorGroup (v ∘ e) from ?_)
    apply (Subgroup.closure_le (fixesVectorGroup (v ∘ e))).mpr
    intro U hU
    change U.val.mulVec (v ∘ e) = v ∘ e
    rcases hU with ⟨a, ha, rfl⟩ | ⟨i, j, rfl⟩
    · funext x
      change (pauliMatrix 0 (physicalXWord a)).mulVec (v ∘ e) x = v (e x)
      exact (physicalXWord_mulVec a v x).trans (congrFun (hX a ha) (e x))
    · funext x
      change (pauliMatrix 0 (physicalZWord (rowPairZMask i j))).mulVec (v ∘ e) x = v (e x)
      exact (physicalZPair_mulVec i j v x).trans (congrFun (hZ i j) (e x))

theorem physicalShorCode_range_eq_stabilizer (r : Fin rows) :
    Set.range (fun v => (physicalShorCode (columns := columns) r).encoding.mulVec v) =
      {v | ∀ U ∈ physicalShorStabilizer rows (columns + 1), U.val.mulVec v = v} := by
  let e := shorBasisEquiv rows (columns + 1)
  ext u
  let v := u ∘ e.symm
  have huv : v ∘ e = u := by
    funext x
    change u (e.symm (e x)) = u x
    rw [Equiv.symm_apply_apply]
  have hfixed := fixed_physicalShorStabilizer_iff v
  rw [huv] at hfixed
  change (u ∈ Set.range (fun c => (physicalShorEncoding rows columns).mulVec c)) ↔
    (∀ U ∈ physicalShorStabilizer rows (columns + 1), U.val.mulVec u = u)
  rw [hfixed]
  change _ ↔ v ∈ {v | (∀ a : Mask rows (columns + 1), xChecks a →
      (basisPermutation (translate a)).mulVec v = v) ∧
      ∀ i j : Fin rows, (shorZPairCheck i j).mulVec v = v}
  rw [← shorEncoding_range_eq_fixedChecks r]
  constructor
  · rintro ⟨c, hc⟩
    let w := c ∘ shorLogicalEquiv.symm
    have hw : w ∘ shorLogicalEquiv = c := by
      funext b
      change c (shorLogicalEquiv.symm (shorLogicalEquiv b)) = c b
      rw [Equiv.symm_apply_apply]
    refine ⟨w, ?_⟩
    funext x
    have he := physicalShorEncoding_mulVec w (e.symm x)
    rw [hw] at he
    change (physicalShorEncoding rows columns).mulVec c (e.symm x) =
      (shorEncoding rows columns).mulVec w (e (e.symm x)) at he
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans (congrFun hc (e.symm x))
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ shorLogicalEquiv, ?_⟩
    funext x
    exact (physicalShorEncoding_mulVec w x).trans
      ((congrFun hw (e x)).trans (congrFun huv x))

theorem physicalShorCode_isStabilizer (r : Fin rows) :
    IsStabilizer (physicalShorCode (columns := columns) r) :=
  ⟨physicalShorStabilizer rows (columns + 1), fun _ hU => physicalShorStabilizer_le_Pauli hU,
    physicalShorCode_range_eq_stabilizer r⟩

theorem physicalShorEncoding_xCheck_fixes (r : Fin rows)
    (a : Mask rows (columns + 1)) (ha : xChecks a) :
    pauliMatrix 0 (physicalXWord a) * (physicalShorCode (columns := columns) r).encoding =
      (physicalShorCode (columns := columns) r).encoding :=
  encoding_fixed_of_fixedSpace _ _ (physicalShorCode_range_eq_stabilizer r)
    (unphasedPauliUnitary (physicalXWord a)) (Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩))

theorem physicalShorEncoding_zPair_fixes (r i j : Fin rows) :
    pauliMatrix 0 (physicalZWord (rowPairZMask (columns := columns + 1) i j)) *
        (physicalShorCode (columns := columns) r).encoding =
      (physicalShorCode (columns := columns) r).encoding :=
  encoding_fixed_of_fixedSpace _ _ (physicalShorCode_range_eq_stabilizer r)
    (unphasedPauliUnitary (physicalZWord (rowPairZMask i j)))
    (Subgroup.subset_closure (Or.inr ⟨i, j, rfl⟩))

#print axioms physicalShorStabilizer
#print axioms physicalShorEncoding_xCheck_fixes
#print axioms physicalShorEncoding_zPair_fixes
#print axioms physicalShorCode_isStabilizer

end CriticalDepth.FaultShorSaturation
