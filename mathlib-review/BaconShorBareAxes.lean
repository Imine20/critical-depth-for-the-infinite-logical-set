import BaconShorSubsystemEncoding
import ShorPhysicalChecks
import ShorPhysicalZChecks
import BinaryPermutationUnitary

/-!
# Protected full-column X and full-row Z for the Bacon--Shor encoding
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary
open scoped BigOperators Kronecker

noncomputable section

variable {m b : ℕ}

private theorem bit_self_add (x : Bit) : x + x = 0 := by decide +revert

private theorem fullColumn_add_self (a : BaconMask m b) : a + a = 0 := by
  funext ij
  exact bit_self_add (a ij)

private theorem logicalBit_add_one (j : Fin 2) :
    qubitBitEquiv (1 - j) = qubitBitEquiv j + 1 := by decide +revert

private theorem membership_add_bareX (ℓ : Bit) (u : Interior m b) (x : BaconMask m b) :
    x + fullXColumn (rows := m + 1) 0 ∈ orbitWords ℓ u ↔
      x ∈ orbitWords (ℓ + 1) u := by
  let a : BaconMask m b := fullXColumn 0
  rw [orbitWords_mem, orbitWords_mem]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← baconWord_add_bareX ℓ u t]
    change baconWord ℓ u t = x + a at ht
    rw [ht, add_assoc, fullColumn_add_self a, add_zero]
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← ht, ← baconWord_add_bareX ℓ u t]
    change baconWord ℓ u t = baconWord ℓ u t + a + a
    rw [add_assoc, fullColumn_add_self a, add_zero]

theorem baconBinaryEncoding_bareX (x : BaconMask m b) (ℓ : Bit) (u : Interior m b) :
    baconBinaryEncoding m b (x + fullXColumn (rows := m + 1) 0) (ℓ, u) =
      baconBinaryEncoding m b x (ℓ + 1, u) := by
  simp only [baconBinaryEncoding, membership_add_bareX]

theorem baconPhysicalEncoding_bareX :
    pauliMatrix 0 (physicalXWord (fullXColumn (rows := m + 1) (0 : Fin (b + 1)))) *
      baconPhysicalEncoding m b =
      baconPhysicalEncoding m b * (SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin (2 ^ (m * b))))) := by
  classical
  ext x a
  let E := shorBasisEquiv (m + 1) (b + 1)
  let g : Fin (2 ^ (m * b)) ≃ Interior m b := gaugeTupleEquiv m b
  let w : BaconMask m b → ℂ := fun y => baconBinaryEncoding m b y (qubitBitEquiv a.1, g a.2)
  have hleft :
      (pauliMatrix 0 (physicalXWord (fullXColumn (rows := m + 1) (0 : Fin (b + 1)))) *
        baconPhysicalEncoding m b) x a =
      baconPhysicalEncoding m b x (1 - a.1, a.2) := by
    change (pauliMatrix 0 (physicalXWord (fullXColumn (rows := m + 1) (0 : Fin (b + 1))))).mulVec
      (w ∘ E) x = _
    rw [physicalXWord_mulVec, shorXCheck_mulVec]
    change baconBinaryEncoding m b (E x + fullXColumn 0) (qubitBitEquiv a.1, g a.2) =
      baconBinaryEncoding m b (E x) (qubitBitEquiv (1 - a.1), g a.2)
    rw [baconBinaryEncoding_bareX, logicalBit_add_one]
  rw [hleft]
  have hcol (j : Fin 2) (k : Fin 2) :
      SinglePauli.X.matrix j k = if j = 1 - k then 1 else 0 := by
    fin_cases j <;> fin_cases k <;> norm_num [SinglePauli.matrix]
  have hk (j : Fin 2 × Fin (2 ^ (m * b))) :
      (SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin (2 ^ (m * b))))) j a =
      if j = (1 - a.1, a.2) then 1 else 0 := by
    rw [Matrix.kronecker_apply, hcol, Matrix.one_apply]
    rcases j with ⟨j₁,j₂⟩
    by_cases h₁ : j₁ = 1 - a.1 <;> by_cases h₂ : j₂ = a.2 <;>
      simp [h₁, h₂, Prod.mk.injEq]
  rw [Matrix.mul_apply]
  simp only [hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem maskDot_fullZRow (x : BaconMask m b) (i : Fin (m + 1)) :
    maskDot x (fullZRow i) = rowParity x i := by
  classical
  simp only [maskDot, Fintype.sum_prod_type, fullZRow, repeatRows, Pi.single_apply, rowParity]
  simp [mul_ite, Finset.sum_ite_eq']

private def logicalParitySign (j : Fin 2) : ℂ := if qubitBitEquiv j = 0 then 1 else -1

theorem baconPhysicalEncoding_bareZ (i : Fin (m + 1)) :
    pauliMatrix 0 (physicalZWord (fullZRow (columns := b + 1) i)) *
      baconPhysicalEncoding m b =
      baconPhysicalEncoding m b * (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin (2 ^ (m * b))))) := by
  classical
  have hz : SinglePauli.Z.matrix = Matrix.diagonal logicalParitySign := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      norm_num [SinglePauli.matrix, Matrix.diagonal_apply, logicalParitySign, qubitBitEquiv]
  have hdiag : (SinglePauli.Z.matrix ⊗ₖ (1 : Operator (Fin (2 ^ (m * b))))) =
      Matrix.diagonal (fun j : Fin 2 × Fin (2 ^ (m * b)) => logicalParitySign j.1) := by
    rw [hz]
    ext ⟨j, g⟩ ⟨k, u⟩
    rw [Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.diagonal_apply]
    by_cases h₁ : j = k <;> by_cases h₂ : g = u <;> simp [h₁, h₂, Prod.mk.injEq]
  rw [hdiag]
  ext x a
  change (pauliMatrix 0 (physicalZWord (fullZRow (columns := b + 1) i))).mulVec
      (fun y => baconPhysicalEncoding m b y a) x = _
  rw [physicalZWord_mulVec, maskDot_fullZRow, Matrix.mul_diagonal]
  let y := shorBasisEquiv (m + 1) (b + 1) x
  let ℓ := qubitBitEquiv a.1
  let u := gaugeTupleEquiv m b a.2
  change (if rowParity y i = 0 then (1 : ℂ) else -1) * baconBinaryEncoding m b y (ℓ,u) =
    baconBinaryEncoding m b y (ℓ,u) * (if ℓ = 0 then 1 else -1)
  by_cases hy : y ∈ orbitWords ℓ u
  · obtain ⟨t, ht⟩ := (orbitWords_mem _ _ _).mp hy
    have hp : rowParity y i = ℓ :=
      (congrArg (fun a => rowParity a i) ht).symm.trans (baconWord_rowParity _ _ _ _)
    rw [hp, mul_comm]
  · simp [baconBinaryEncoding, hy]

#print axioms baconPhysicalEncoding_bareX
#print axioms baconPhysicalEncoding_bareZ

end

end CriticalDepth.FaultShorSaturation.BaconShor
