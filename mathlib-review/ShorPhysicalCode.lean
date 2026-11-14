import ShorPhysicalChecks
import PauliGroup

/-!
# Physical qubit indexing of the rectangular Shor encoding

The basis equivalence enumerates every rectangular bit string as a
computational basis word on its full qubit register. The same reindexing is
used in the physical encoding and in the action of its tensor X checks.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary
open CriticalDepth.ReviewV2.PauliRowAction
open scoped BigOperators

variable {rows columns : ℕ}

/-- Binary field elements and computational-basis bits in the same order. -/
def qubitBitEquiv : Fin 2 ≃ Bit where
  toFun x := if x = 0 then 0 else 1
  invFun b := if b = 0 then 0 else 1
  left_inv := by decide
  right_inv := by decide

def shorSiteEquiv (rows columns : ℕ) :
    Fin (rows * columns) ≃ Fin rows × Fin columns := finProdFinEquiv.symm

def shorBasisEquiv (rows columns : ℕ) : QubitBasis (rows * columns) ≃ Mask rows columns where
  toFun x ij := qubitBitEquiv (x ((shorSiteEquiv rows columns).symm ij))
  invFun x s := qubitBitEquiv.symm (x (shorSiteEquiv rows columns s))
  left_inv x := by
    funext s
    change qubitBitEquiv.symm (qubitBitEquiv
      (x ((shorSiteEquiv rows columns).symm (shorSiteEquiv rows columns s)))) = x s
    rw [qubitBitEquiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv x := by
    funext ij
    simp

def shorLogicalEquiv : Fin 2 × Fin 1 ≃ Bit :=
  (Equiv.prodUnique (Fin 2) (Fin 1)).trans qubitBitEquiv

/-- The physical encoding uses all rectangular computational-basis words. -/
noncomputable def physicalShorEncoding (rows columns : ℕ) :
    Matrix (QubitBasis (rows * (columns + 1))) (Fin 2 × Fin 1) ℂ :=
  fun x b => shorEncoding rows columns (shorBasisEquiv rows (columns + 1) x) (shorLogicalEquiv b)

theorem physicalShorEncoding_isometry (r : Fin rows) :
    (physicalShorEncoding rows columns).conjTranspose * physicalShorEncoding rows columns = 1 := by
  classical
  let : Nonempty (Fin rows) := ⟨r⟩
  ext a b
  change (∑ x : QubitBasis (rows * (columns + 1)),
    star (shorEncoding rows columns (shorBasisEquiv rows (columns + 1) x) (shorLogicalEquiv a)) *
      shorEncoding rows columns (shorBasisEquiv rows (columns + 1) x) (shorLogicalEquiv b)) = _
  rw [(shorBasisEquiv rows (columns + 1)).sum_comp
    (fun x => star (shorEncoding rows columns x (shorLogicalEquiv a)) *
      shorEncoding rows columns x (shorLogicalEquiv b))]
  change ((shorEncoding rows columns).conjTranspose * shorEncoding rows columns)
    (shorLogicalEquiv a) (shorLogicalEquiv b) = _
  rw [shorEncoding_isometric]
  by_cases h : a = b
  · subst b
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne (fun hh => h (shorLogicalEquiv.injective hh)), Matrix.one_apply_ne h]

/-- Registered as a one-logical-qubit subspace code in the native model. -/
noncomputable def physicalShorCode (r : Fin rows) :
    Code (rows * (columns + 1)) (fun _ => 2) (2 ^ 1) 1 :=
  ⟨physicalShorEncoding rows columns, physicalShorEncoding_isometry r⟩

theorem physicalShorEncoding_mulVec (w : Bit → ℂ) (x : QubitBasis (rows * (columns + 1))) :
    (physicalShorEncoding rows columns).mulVec (w ∘ shorLogicalEquiv) x =
      (shorEncoding rows columns).mulVec w (shorBasisEquiv rows (columns + 1) x) := by
  unfold Matrix.mulVec dotProduct
  exact shorLogicalEquiv.sum_comp
    (fun b => shorEncoding rows columns (shorBasisEquiv rows (columns + 1) x) b * w b)

/-- The physical X word indexed by a rectangular mask. -/
def physicalXWord (a : Mask rows columns) (s : Fin (rows * columns)) : SinglePauli :=
  if a (shorSiteEquiv rows columns s) = 0 then .I else .X

private theorem qubitBitEquiv_singleFlip (b : Fin 2) (a : Bit) :
    qubitBitEquiv (singleFlip (if a = 0 then .I else .X) b) = qubitBitEquiv b + a := by
  decide +revert

private theorem shorBasisEquiv_flipWord (a : Mask rows columns)
    (x : QubitBasis (rows * columns)) :
    shorBasisEquiv rows columns (flipWord (physicalXWord a) x) = shorBasisEquiv rows columns x + a := by
  funext ij
  change qubitBitEquiv (singleFlip
      (if a (shorSiteEquiv rows columns ((shorSiteEquiv rows columns).symm ij)) = 0 then .I else .X)
      (x ((shorSiteEquiv rows columns).symm ij))) =
    qubitBitEquiv (x ((shorSiteEquiv rows columns).symm ij)) + a ij
  rw [Equiv.apply_symm_apply]
  exact qubitBitEquiv_singleFlip _ _

theorem physicalXWord_mulVec (a : Mask rows columns) (v : Mask rows columns → ℂ)
    (x : QubitBasis (rows * columns)) :
    (pauliMatrix 0 (physicalXWord a)).mulVec (v ∘ shorBasisEquiv rows columns) x =
      (basisPermutation (translate a)).mulVec v (shorBasisEquiv rows columns x) := by
  classical
  have hcoeff : rowCoefficient (physicalXWord a) x = 1 := by
    apply Finset.prod_eq_one
    intro s _
    unfold physicalXWord
    split <;> rfl
  simp only [Matrix.mulVec, dotProduct, pauliMatrix_row, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hcoeff, one_mul,
    Function.comp_apply, shorBasisEquiv_flipWord]
  symm
  exact shorXCheck_mulVec a v (shorBasisEquiv rows columns x)

#print axioms physicalShorEncoding_isometry
#print axioms physicalShorCode
#print axioms physicalShorEncoding_mulVec
#print axioms physicalXWord_mulVec

end CriticalDepth.FaultShorSaturation
