import ShorDistanceDetection

/-!
# A physical Pauli witness for rectangular Shor distance

When the column count is at most the row count, any full row of tensor Z
has precisely the distance weight. Its logical action is the diagonal
sign of the common encoded parity.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript
open scoped BigOperators Kronecker

variable {rows columns : ℕ}

private theorem maskDot_fullZRow (x : Mask rows columns) (i : Fin rows) :
    maskDot x (fullZRow i) = rowParity x i := by
  classical
  simp only [maskDot, Fintype.sum_prod_type, fullZRow, repeatRows, Pi.single_apply, rowParity]
  simp [mul_ite, Finset.sum_ite_eq']

private theorem fullZRow_support_card (i : Fin rows) :
    (pauliSupport (physicalZWord (fullZRow (columns := columns) i))).card = columns := by
  classical
  let e := shorSiteEquiv rows columns
  have hmap : (pauliSupport (physicalZWord (fullZRow (columns := columns) i))).map e.toEmbedding =
      support (0 : Mask rows columns) (fullZRow i) := by
    ext a
    obtain ⟨s, rfl⟩ := e.surjective a
    constructor
    · intro hs
      obtain ⟨t, ht, he⟩ := Finset.mem_map.mp hs
      have hts : t = s := e.injective he
      subst t
      have hn : fullZRow (columns := columns) i (e s) ≠ 0 := by
        intro h
        have h' : (fullZRow (columns := columns) i) (shorSiteEquiv rows columns s) = 0 := h
        have hf := (Finset.mem_filter.mp ht).2
        exact hf (by simp [physicalZWord, h'])
      simp [support, hn]
    · intro hs
      have hn : fullZRow (columns := columns) i (e s) ≠ 0 := by
        simpa [support] using hs
      refine Finset.mem_map.mpr ⟨s, ?_, rfl⟩
      have h' : (fullZRow (columns := columns) i) (shorSiteEquiv rows columns s) ≠ 0 := hn
      simp [pauliSupport, physicalZWord, h']
  calc
    (pauliSupport (physicalZWord (fullZRow (columns := columns) i))).card =
        ((pauliSupport (physicalZWord (fullZRow (columns := columns) i))).map e.toEmbedding).card :=
      by rw [Finset.card_map]
    _ = (support (0 : Mask rows columns) (fullZRow i)).card := congrArg Finset.card hmap
    _ = columns := fullZRow_weight i

private def logicalZ (b : Fin 2 × Fin 1) : ℂ := if shorLogicalEquiv b = 0 then 1 else -1

theorem physicalShorEncoding_fullZRow (i : Fin rows) :
    pauliMatrix 0 (physicalZWord (fullZRow (columns := columns + 1) i)) *
      physicalShorEncoding rows columns =
        physicalShorEncoding rows columns * Matrix.diagonal logicalZ := by
  classical
  ext x b
  change (pauliMatrix 0 (physicalZWord (fullZRow (columns := columns + 1) i))).mulVec
    (fun y => physicalShorEncoding rows columns y b) x = _
  rw [physicalZWord_mulVec, maskDot_fullZRow, Matrix.mul_diagonal]
  let word := shorBasisEquiv rows (columns + 1) x
  let bit := shorLogicalEquiv b
  change (if rowParity word i = 0 then (1 : ℂ) else -1) *
      shorEncoding rows columns word bit =
    shorEncoding rows columns word bit * (if bit = 0 then 1 else -1)
  by_cases h : word ∈ parityWords bit
  · have hp := (parityWords_mem_iff bit word).mp h i
    rw [hp, mul_comm]
  · simp [shorEncoding, h]

theorem physicalShorCode_hasActualDistance (i : Fin rows) (hside : columns + 1 ≤ rows) :
    HasActualDistance (physicalShorCode (columns := columns) i) (columns + 1) := by
  let C := physicalShorCode (columns := columns) i
  let p := physicalZWord (fullZRow (columns := columns + 1) i)
  change HasActualDistance C (columns + 1)
  refine ⟨?_, pauliSupport p, fullZRow_support_card i, pauliMatrix 0 p,
    pauliMatrix_supportedOn_pauliSupport p, ?_⟩
  · simpa [min_eq_right hside] using physicalShorCode_detectsBelow (columns := columns) i
  · have hact : pauliMatrix 0 p * C.encoding = C.encoding * Matrix.diagonal logicalZ :=
      physicalShorEncoding_fullZRow i
    rintro ⟨M, hM⟩
    have hcomp : C.encoding.conjTranspose * (pauliMatrix 0 p) * C.encoding =
        Matrix.diagonal logicalZ := by
      rw [Matrix.mul_assoc, hact, ← Matrix.mul_assoc, C.isometry, Matrix.one_mul]
    rw [hcomp] at hM
    have h₀ := congrArg (fun A : Operator (Fin 2 × Fin 1) => A (0, 0) (0, 0)) hM
    have h₁ := congrArg (fun A : Operator (Fin 2 × Fin 1) => A (1, 0) (1, 0)) hM
    have hzero : shorLogicalEquiv (0, 0) = 0 := by decide
    have hone : shorLogicalEquiv (1, 0) ≠ 0 := by decide
    have hpos : (1 : ℂ) = M 0 0 := by
      change Matrix.diagonal logicalZ (0, 0) (0, 0) =
        ((1 : Operator (Fin 2)) ⊗ₖ M) (0, 0) (0, 0) at h₀
      simpa only [Matrix.diagonal_apply_eq, logicalZ, hzero, ite_true,
        Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul] using h₀
    have hneg : (-1 : ℂ) = M 0 0 := by
      change Matrix.diagonal logicalZ (1, 0) (1, 0) =
        ((1 : Operator (Fin 2)) ⊗ₖ M) (1, 0) (1, 0) at h₁
      simpa only [Matrix.diagonal_apply_eq, logicalZ, hone, ite_false,
        Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul] using h₁
    have hbad : (1 : ℂ) = -1 := hpos.trans hneg.symm
    norm_num at hbad

#print axioms physicalShorEncoding_fullZRow
#print axioms physicalShorCode_hasActualDistance

end CriticalDepth.FaultShorSaturation
