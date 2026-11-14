import BaconShorGaugeCoordinates
import BaconShorBareAxes
import ShorPauliMasks

/-!
# Physical Bacon--Shor gauge actions

The row-even X masks act as a permutation on the gauge factor.
The column-even Z masks are diagonal on that factor.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary
open scoped BigOperators Kronecker

noncomputable section

variable {m b : ℕ}

private def gaugeTranslation (a : Interior m b) : Equiv.Perm (Interior m b) where
  toFun u := u + a
  invFun u := u - a
  left_inv u := add_sub_cancel_right u a
  right_inv u := sub_add_cancel u a

private def baconGaugeXPerm (a : BaconMask m b) : Equiv.Perm (Fin (2 ^ (m * b))) :=
  ((gaugeTupleEquiv m b).trans (gaugeTranslation (gaugeBits a))).trans (gaugeTupleEquiv m b).symm

private theorem baconGaugeXPerm_apply (a : BaconMask m b) (v : Fin (2 ^ (m * b))) :
    gaugeTupleEquiv m b (baconGaugeXPerm a v) = gaugeTupleEquiv m b v + gaugeBits a := by
  unfold baconGaugeXPerm
  rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem baconPhysicalEncoding_gaugeX (a : BaconMask m b) (ha : gaugeX a) :
    pauliMatrix 0 (physicalXWord a) * baconPhysicalEncoding m b =
      baconPhysicalEncoding m b * ((1 : Operator (Fin 2)) ⊗ₖ basisPermutation (baconGaugeXPerm a)) := by
  classical
  ext x j
  let E := shorBasisEquiv (m + 1) (b + 1)
  let g : Fin (2 ^ (m * b)) ≃ Interior m b := gaugeTupleEquiv m b
  let v : BaconMask m b → ℂ := fun w => baconBinaryEncoding m b w (qubitBitEquiv j.1, g j.2)
  have hleft :
      (pauliMatrix 0 (physicalXWord a) * baconPhysicalEncoding m b) x j =
      baconPhysicalEncoding m b x (j.1, baconGaugeXPerm a j.2) := by
    change (pauliMatrix 0 (physicalXWord a)).mulVec (v ∘ E) x = _
    rw [physicalXWord_mulVec, shorXCheck_mulVec]
    change baconBinaryEncoding m b (E x + a) (qubitBitEquiv j.1, g j.2) =
      baconBinaryEncoding m b (E x) (qubitBitEquiv j.1, g (baconGaugeXPerm a j.2))
    rw [baconBinaryEncoding_gaugeX a ha, baconGaugeXPerm_apply]
  rw [hleft]
  have hk (k : Fin 2 × Fin (2 ^ (m * b))) :
      ((1 : Operator (Fin 2)) ⊗ₖ basisPermutation (baconGaugeXPerm a)) k j =
        if k = (j.1, baconGaugeXPerm a j.2) then 1 else 0 := by
    rw [Matrix.kronecker_apply, Matrix.one_apply, basisPermutation_apply]
    rcases k with ⟨k₁,k₂⟩
    by_cases h₁ : k₁ = j.1 <;> by_cases h₂ : k₂ = baconGaugeXPerm a j.2 <;>
      simp [h₁, h₂, Prod.mk.injEq]
  rw [Matrix.mul_apply]
  simp only [hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private def baconGaugeZSign (z : BaconMask m b) (u : Fin (2 ^ (m * b))) : ℂ :=
  if maskDot (baconWord 0 (gaugeTupleEquiv m b u) 0) z = 0 then 1 else -1

theorem baconPhysicalEncoding_gaugeZ (z : BaconMask m b) (hz : gaugeZ z) :
    pauliMatrix 0 (physicalZWord z) * baconPhysicalEncoding m b =
      baconPhysicalEncoding m b * ((1 : Operator (Fin 2)) ⊗ₖ Matrix.diagonal (baconGaugeZSign z)) := by
  classical
  have hdiag : ((1 : Operator (Fin 2)) ⊗ₖ Matrix.diagonal (baconGaugeZSign z)) =
      Matrix.diagonal (fun j : Fin 2 × Fin (2 ^ (m * b)) => baconGaugeZSign z j.2) := by
    ext ⟨a,g⟩ ⟨b,u⟩
    rw [Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h₁ : a = b <;> by_cases h₂ : g = u <;> simp [h₁, h₂, Prod.mk.injEq]
  rw [hdiag]
  ext x j
  change (pauliMatrix 0 (physicalZWord z)).mulVec (fun y => baconPhysicalEncoding m b y j) x = _
  rw [physicalZWord_mulVec, Matrix.mul_diagonal]
  let y := shorBasisEquiv (m + 1) (b + 1) x
  let ℓ := qubitBitEquiv j.1
  let u := gaugeTupleEquiv m b j.2
  change (if maskDot y z = 0 then (1 : ℂ) else -1) * baconBinaryEncoding m b y (ℓ,u) =
    baconBinaryEncoding m b y (ℓ,u) * (if maskDot (baconWord 0 u 0) z = 0 then 1 else -1)
  by_cases hy : y ∈ orbitWords ℓ u
  · obtain ⟨t, ht⟩ := (orbitWords_mem _ _ _).mp hy
    rw [← ht, baconWord_dot_gaugeZ ℓ u t z hz, mul_comm]
  · simp [baconBinaryEncoding, hy]

theorem baconGaugeOnly_X (a : BaconMask m b) (ha : gaugeX a) :
    GaugeOnly (baconShorCode m b) (pauliMatrix 0 (physicalXWord a)) := by
  refine ⟨basisPermutation (baconGaugeXPerm a), ?_⟩
  change (baconPhysicalEncoding m b).conjTranspose * pauliMatrix 0 (physicalXWord a) *
    baconPhysicalEncoding m b = _
  rw [Matrix.mul_assoc, baconPhysicalEncoding_gaugeX a ha, ← Matrix.mul_assoc,
    baconPhysicalEncoding_isometric, Matrix.one_mul]

theorem baconGaugeOnly_Z (z : BaconMask m b) (hz : gaugeZ z) :
    GaugeOnly (baconShorCode m b) (pauliMatrix 0 (physicalZWord z)) := by
  refine ⟨Matrix.diagonal (baconGaugeZSign z), ?_⟩
  change (baconPhysicalEncoding m b).conjTranspose * pauliMatrix 0 (physicalZWord z) *
    baconPhysicalEncoding m b = _
  rw [Matrix.mul_assoc, baconPhysicalEncoding_gaugeZ z hz, ← Matrix.mul_assoc,
    baconPhysicalEncoding_isometric, Matrix.one_mul]

theorem baconGaugeOnly_XZ (a z : BaconMask m b) (ha : gaugeX a) (hz : gaugeZ z) :
    GaugeOnly (baconShorCode m b) (pauliMatrix 0 (physicalXWord a) * pauliMatrix 0 (physicalZWord z)) := by
  refine ⟨basisPermutation (baconGaugeXPerm a) * Matrix.diagonal (baconGaugeZSign z), ?_⟩
  change (baconPhysicalEncoding m b).conjTranspose *
    (pauliMatrix 0 (physicalXWord a) * pauliMatrix 0 (physicalZWord z)) *
    baconPhysicalEncoding m b = _
  simp only [Matrix.mul_assoc]
  rw [baconPhysicalEncoding_gaugeZ z hz, ← Matrix.mul_assoc (pauliMatrix 0 (physicalXWord a)),
    baconPhysicalEncoding_gaugeX a ha, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, ← Matrix.mul_assoc, baconPhysicalEncoding_isometric, Matrix.one_mul]

#print axioms baconPhysicalEncoding_gaugeX
#print axioms baconPhysicalEncoding_gaugeZ
#print axioms baconGaugeOnly_XZ

end

end CriticalDepth.FaultShorSaturation.BaconShor
