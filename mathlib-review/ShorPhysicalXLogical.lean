import ShorPhysicalCode

/-!
# Action of a full physical X column on the Shor encoding
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary
open scoped BigOperators Kronecker

variable {rows columns : ℕ}

private def bitFlip : Equiv.Perm Bit where
  toFun b := b + 1
  invFun b := b + 1
  left_inv := by decide
  right_inv := by decide

private def encodedBitFlip : Equiv.Perm (Fin 2 × Fin 1) :=
  (shorLogicalEquiv.trans bitFlip).trans shorLogicalEquiv.symm

private theorem encodedBitFlip_logical (b : Fin 2 × Fin 1) :
    shorLogicalEquiv (encodedBitFlip b) = shorLogicalEquiv b + 1 := by
  unfold encodedBitFlip
  simp [bitFlip]

theorem fullXColumn_support_card (j : Fin columns) :
    (pauliSupport (physicalXWord (fullXColumn (rows := rows) j))).card = rows := by
  classical
  let e := shorSiteEquiv rows columns
  have hmap : (pauliSupport (physicalXWord (fullXColumn (rows := rows) j))).map e.toEmbedding =
      support (fullXColumn j) (0 : Mask rows columns) := by
    ext a
    obtain ⟨s, rfl⟩ := e.surjective a
    rw [Finset.mem_map_equiv]
    change _ ↔ e s ∈ support (fullXColumn j) (0 : Mask rows columns)
    simp only [Equiv.symm_apply_apply, pauliSupport, support, Finset.mem_filter,
      Finset.mem_univ, true_and, Pi.zero_apply, ne_eq, not_true_eq_false, or_false]
    change (if fullXColumn (rows := rows) j (e s) = 0 then SinglePauli.I else .X) ≠ .I ↔ _
    by_cases h : fullXColumn (rows := rows) j (e s) = 0 <;> simp [h]
  calc
    (pauliSupport (physicalXWord (fullXColumn (rows := rows) j))).card =
        ((pauliSupport (physicalXWord (fullXColumn (rows := rows) j))).map e.toEmbedding).card :=
      by rw [Finset.card_map]
    _ = (support (fullXColumn j) (0 : Mask rows columns)).card := congrArg Finset.card hmap
    _ = rows := fullXColumn_weight j

theorem physicalShorEncoding_fullXColumn (j : Fin (columns + 1)) :
    pauliMatrix 0 (physicalXWord (fullXColumn (rows := rows) j)) *
      physicalShorEncoding rows columns =
        physicalShorEncoding rows columns * (SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin 1))) := by
  classical
  have hperm : basisPermutation encodedBitFlip =
      SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin 1)) := by
    ext ⟨a, p⟩ ⟨b, q⟩
    fin_cases p
    fin_cases q
    fin_cases a <;> fin_cases b <;>
      norm_num [basisPermutation_apply, encodedBitFlip, shorLogicalEquiv, qubitBitEquiv, bitFlip,
        SinglePauli.matrix, Matrix.kronecker_apply, Matrix.one_apply] <;> decide
  rw [← hperm]
  ext x b
  let e := shorBasisEquiv rows (columns + 1)
  let W := fun y => shorEncoding rows columns y (shorLogicalEquiv b)
  change (pauliMatrix 0 (physicalXWord (fullXColumn (rows := rows) j))).mulVec (W ∘ e) x = _
  rw [physicalXWord_mulVec]
  change (basisPermutation (translate (fullXColumn (rows := rows) j)) *
    shorEncoding rows columns) (e x) (shorLogicalEquiv b) = _
  rw [fullXColumnPermutation_shorEncoding_apply, ← encodedBitFlip_logical]
  symm
  simp only [Matrix.mul_apply, basisPermutation_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

#print axioms fullXColumn_support_card
#print axioms physicalShorEncoding_fullXColumn

end CriticalDepth.FaultShorSaturation
