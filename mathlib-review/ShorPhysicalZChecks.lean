import ShorPhysicalCode

/-!
# Physical full-row Z checks of the rectangular Shor code

The computational-basis phase of a tensor Z mask is the character of
its binary dot product. Two full rows give the dot product equal to
the sum of their row parities.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.ReviewV2.PauliRowAction
open scoped BigOperators

variable {rows columns : ℕ}

private def bitSign (x : Bit) : ℂ :=
  if x = 0 then 1 else -1

private theorem bit_eq_zero_or_one (x : Bit) : x = 0 ∨ x = 1 := by
  decide +revert

private theorem bit_two : (1 : Bit) + 1 = 0 := by decide

private theorem bitSign_add (x y : Bit) : bitSign (x + y) = bitSign x * bitSign y := by
  rcases bit_eq_zero_or_one x with (rfl | rfl) <;>
    rcases bit_eq_zero_or_one y with (rfl | rfl) <;>
    simp [bitSign, bit_two]

private theorem bitSign_sum {ι : Type*} (S : Finset ι) (f : ι → Bit) :
    bitSign (∑ i ∈ S, f i) = ∏ i ∈ S, bitSign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [bitSign]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bitSign_add, ih]

/-- The physical bare Z word indexed by a rectangular mask. -/
def physicalZWord (a : Mask rows columns) (s : Fin (rows * columns)) : SinglePauli :=
  if a (shorSiteEquiv rows columns s) = 0 then .I else .Z

private theorem singleCoefficient_Z_mask (x : Fin 2) (b : Bit) :
    singleCoefficient (if b = 0 then .I else .Z) x = bitSign (qubitBitEquiv x * b) := by
  fin_cases x <;> rcases bit_eq_zero_or_one b with (rfl | rfl) <;>
    simp [singleCoefficient, qubitBitEquiv, bitSign]

private theorem physicalZWord_flip (a : Mask rows columns) (x : QubitBasis (rows * columns)) :
    flipWord (physicalZWord a) x = x := by
  funext s
  unfold flipWord physicalZWord
  split <;> rfl

theorem physicalZWord_mulVec (a : Mask rows columns)
    (v : QubitBasis (rows * columns) → ℂ) (x : QubitBasis (rows * columns)) :
    (pauliMatrix 0 (physicalZWord a)).mulVec v x =
      bitSign (maskDot (shorBasisEquiv rows columns x) a) * v x := by
  classical
  have hsign : rowCoefficient (physicalZWord a) x =
      bitSign (maskDot (shorBasisEquiv rows columns x) a) := by
    unfold rowCoefficient maskDot
    rw [bitSign_sum]
    simp only [physicalZWord, singleCoefficient_Z_mask]
    let e := shorSiteEquiv rows columns
    change (∏ s, bitSign (qubitBitEquiv (x s) * a (e s))) =
      ∏ ij, bitSign (qubitBitEquiv (x (e.symm ij)) * a ij)
    calc
      (∏ s, bitSign (qubitBitEquiv (x s) * a (e s))) =
          ∏ s, bitSign (qubitBitEquiv (x (e.symm (e s))) * a (e s)) := by
        apply Finset.prod_congr rfl
        intro s _
        have hs : e.symm (e s) = s := e.symm_apply_apply s
        rw [hs]
      _ = ∏ ij, bitSign (qubitBitEquiv (x (e.symm ij)) * a ij) :=
        e.prod_comp (fun ij => bitSign (qubitBitEquiv (x (e.symm ij)) * a ij))
  simp only [Matrix.mulVec, dotProduct, pauliMatrix_row, ite_mul, zero_mul, physicalZWord_flip]
  simp [hsign]

/-- The sum of the all-Z masks of two rows. Equal row indices give zero. -/
def rowPairZMask (i j : Fin rows) : Mask rows columns :=
  repeatRows (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))

theorem maskDot_rowPairZMask (x : Mask rows columns) (i j : Fin rows) :
    maskDot x (rowPairZMask i j) = rowParity x i + rowParity x j := by
  classical
  simp only [maskDot, Fintype.sum_prod_type, rowPairZMask, repeatRows,
    mul_add, Finset.sum_add_distrib, rowParity]
  simp [mul_ite, Finset.sum_ite_eq']

private theorem bitSign_add_pair (x y : Bit) :
    bitSign (x + y) = if x = y then 1 else -1 := by
  rcases bit_eq_zero_or_one x with (rfl | rfl) <;>
    rcases bit_eq_zero_or_one y with (rfl | rfl) <;>
    simp [bitSign, bit_two]

theorem physicalZPair_mulVec (i j : Fin rows) (v : Mask rows columns → ℂ)
    (x : QubitBasis (rows * columns)) :
    (pauliMatrix 0 (physicalZWord (rowPairZMask i j))).mulVec
      (v ∘ shorBasisEquiv rows columns) x =
      (shorZPairCheck i j).mulVec v (shorBasisEquiv rows columns x) := by
  rw [physicalZWord_mulVec, maskDot_rowPairZMask, bitSign_add_pair, shorZPairCheck_mulVec]
  rfl

#print axioms physicalZWord_mulVec
#print axioms maskDot_rowPairZMask
#print axioms physicalZPair_mulVec

end CriticalDepth.FaultShorSaturation
