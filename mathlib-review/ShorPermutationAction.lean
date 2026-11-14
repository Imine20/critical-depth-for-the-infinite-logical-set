import BinaryPermutationUnitary

/-!
# Action of reversible columnwise row maps on the rectangular Shor encoding

A row map that fixes the all-ones mask preserves each common-parity coset
when applied in every column. A full-column X mask acts on the same encoding
by flipping the common parity.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.BinaryPermutationUnitary

variable {rows columns : ℕ}

/-- The simultaneous action on all columns of a reversible row map. -/
def acrossColumnsLinearEquiv (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) :
    Mask rows columns ≃ₗ[Bit] Mask rows columns where
  toFun := acrossColumns T.toLinearMap
  invFun := acrossColumns T.symm.toLinearMap
  left_inv a := by
    funext ij
    exact congrFun (T.symm_apply_apply (fun i => a (i, ij.2))) ij.1
  right_inv a := by
    funext ij
    exact congrFun (T.apply_symm_apply (fun i => a (i, ij.2))) ij.1
  map_add' a b := by
    funext ij
    exact congrFun (T.map_add (fun i => a (i, ij.2)) (fun i => b (i, ij.2))) ij.1
  map_smul' t a := by
    funext ij
    exact congrFun (T.map_smul t (fun i => a (i, ij.2))) ij.1

private theorem bit_eq_zero_or_one (b : Bit) : b = 0 ∨ b = 1 := by
  decide +revert

theorem acrossColumnsLinearEquiv_parityWords
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit))
    (hT : T (1 : Fin rows → Bit) = 1) (x : Mask rows (columns + 1)) (b : Bit) :
    acrossColumnsLinearEquiv T x ∈ parityWords b ↔ x ∈ parityWords b := by
  have hconst : T (fun _ => b) = fun _ => b := by
    rcases bit_eq_zero_or_one b with rfl | rfl
    · exact T.map_zero
    · exact hT
  simp only [parityWords_mem_iff, ← funext_iff]
  change (fun i => rowParity (acrossColumns T.toLinearMap x) i) = (fun _ => b) ↔
    (fun i => rowParity x i) = (fun _ => b)
  rw [rowParity_acrossColumns]
  change T (fun i => rowParity x i) = (fun _ => b) ↔ _
  constructor
  · intro h
    exact T.injective (h.trans hconst.symm)
  · intro h
    exact (congrArg T h).trans hconst

theorem acrossColumnsPermutation_fixes_shorEncoding
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit))
    (hT : T (1 : Fin rows → Bit) = 1) :
    basisPermutation (acrossColumnsLinearEquiv (columns := columns + 1) T).toEquiv *
      shorEncoding rows columns = shorEncoding rows columns := by
  classical
  ext x b
  rw [basisPermutation_mul_apply]
  have hmem := acrossColumnsLinearEquiv_parityWords T hT
    ((acrossColumnsLinearEquiv (columns := columns + 1) T).symm x) b
  rw [LinearEquiv.apply_symm_apply] at hmem
  change shorEncoding rows columns
    ((acrossColumnsLinearEquiv (columns := columns + 1) T).symm x) b = _
  simp only [shorEncoding, hmem]

/-- A full-column X acts as the logical bit flip in the parity-coset basis. -/
theorem fullXColumnPermutation_shorEncoding_apply (j : Fin (columns + 1))
    (x : Mask rows (columns + 1)) (b : Bit) :
    (basisPermutation (translate (fullXColumn (rows := rows) j)) *
      shorEncoding rows columns) x b =
      shorEncoding rows columns x (b + 1) := by
  classical
  rw [basisPermutation_mul_apply]
  have hparity (i : Fin rows) :
      rowParity (x - fullXColumn j) i = rowParity x i - 1 := by
    simp [rowParity, Pi.sub_apply, Finset.sum_sub_distrib, fullXColumn,
      Finset.sum_ite_eq']
  have hmem : x - fullXColumn j ∈ parityWords b ↔ x ∈ parityWords (b + 1) := by
    simp only [parityWords_mem_iff, hparity, sub_eq_iff_eq_add]
  change shorEncoding rows columns (x - fullXColumn j) b = _
  simp only [shorEncoding, hmem]

#print axioms acrossColumnsLinearEquiv_parityWords
#print axioms acrossColumnsPermutation_fixes_shorEncoding
#print axioms fullXColumnPermutation_shorEncoding_apply

end CriticalDepth.FaultShorSaturation
