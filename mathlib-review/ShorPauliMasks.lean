import ShorPhysicalZChecks

/-!
# Binary masks of physical Pauli words on a rectangular register

The mask pair records the X and Z components of the word, its physical
support cardinality, the phases of commutation against pure X and Z
checks, and its decomposition into the two pure Pauli words.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript
open scoped BigOperators

variable {rows columns : ℕ}

private def xBit : SinglePauli → Bit
  | .I | .Z => 0
  | .X | .Y => 1

private def zBit : SinglePauli → Bit
  | .I | .X => 0
  | .Y | .Z => 1

def xMaskOfPauli (p : Fin (rows * columns) → SinglePauli) : Mask rows columns :=
  fun ij => xBit (p ((shorSiteEquiv rows columns).symm ij))

def zMaskOfPauli (p : Fin (rows * columns) → SinglePauli) : Mask rows columns :=
  fun ij => zBit (p ((shorSiteEquiv rows columns).symm ij))

theorem pauliSupport_card_eq_rectangular (p : Fin (rows * columns) → SinglePauli) :
    (pauliSupport p).card = (support (xMaskOfPauli p) (zMaskOfPauli p)).card := by
  classical
  have hmap : (pauliSupport p).map (shorSiteEquiv rows columns).toEmbedding =
      support (xMaskOfPauli p) (zMaskOfPauli p) := by
    ext ij
    obtain ⟨s, rfl⟩ := (shorSiteEquiv rows columns).surjective ij
    rw [Finset.mem_map_equiv]
    change _ ↔ (shorSiteEquiv rows columns) s ∈ support (xMaskOfPauli p) (zMaskOfPauli p)
    rw [show (shorSiteEquiv rows columns).symm ((shorSiteEquiv rows columns) s) = s
      from (shorSiteEquiv rows columns).symm_apply_apply s]
    change s ∈ Finset.univ.filter (fun i => p i ≠ .I) ↔
      (shorSiteEquiv rows columns) s ∈
        Finset.univ.filter (fun ij => xMaskOfPauli p ij ≠ 0 ∨ zMaskOfPauli p ij ≠ 0)
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    change p s ≠ .I ↔
      xBit (p ((shorSiteEquiv rows columns).symm ((shorSiteEquiv rows columns) s))) ≠ 0 ∨
      zBit (p ((shorSiteEquiv rows columns).symm ((shorSiteEquiv rows columns) s))) ≠ 0
    have hs : (shorSiteEquiv rows columns).symm ((shorSiteEquiv rows columns) s) = s :=
      (shorSiteEquiv rows columns).symm_apply_apply s
    rw [hs]
    cases p s <;> simp [xBit, zBit]
  rw [← hmap, Finset.card_map]

/-- A binary parity as a commutation sign. -/
def pauliParitySign (b : Bit) : ℂ := if b = 0 then 1 else -1

private theorem bit_eq_zero_or_one (b : Bit) : b = 0 ∨ b = 1 := by
  decide +revert

private theorem one_add_one_bit : (1 : Bit) + 1 = 0 := by decide

private theorem paritySign_add (a b : Bit) :
    pauliParitySign (a + b) = pauliParitySign a * pauliParitySign b := by
  rcases bit_eq_zero_or_one a with (rfl | rfl) <;>
    rcases bit_eq_zero_or_one b with (rfl | rfl) <;>
    simp [pauliParitySign, one_add_one_bit]

private theorem paritySign_sum {ι : Type*} (S : Finset ι) (f : ι → Bit) :
    pauliParitySign (∑ i ∈ S, f i) = ∏ i ∈ S, pauliParitySign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pauliParitySign]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, paritySign_add, ih]

private theorem singleX_commutation (a : Bit) (p : SinglePauli) :
    (if a = 0 then SinglePauli.I else SinglePauli.X).commutationSign p =
      pauliParitySign (zBit p * a) := by
  rcases bit_eq_zero_or_one a with (rfl | rfl) <;> cases p <;>
    simp [SinglePauli.commutationSign, pauliParitySign, zBit]

private theorem singleZ_commutation (a : Bit) (p : SinglePauli) :
    (if a = 0 then SinglePauli.I else SinglePauli.Z).commutationSign p =
      pauliParitySign (xBit p * a) := by
  rcases bit_eq_zero_or_one a with (rfl | rfl) <;> cases p <;>
    simp [SinglePauli.commutationSign, pauliParitySign, xBit]

theorem physicalX_commutation (a : Mask rows columns) (p : Fin (rows * columns) → SinglePauli) :
    pauliMatrix 0 (physicalXWord a) * pauliMatrix 0 p =
      pauliParitySign (maskDot (zMaskOfPauli p) a) •
        (pauliMatrix 0 p * pauliMatrix 0 (physicalXWord a)) := by
  rw [unphased_pauliMatrix_commutation]
  congr 1
  unfold maskDot
  rw [paritySign_sum]
  simp only [physicalXWord, singleX_commutation, zMaskOfPauli]
  let e := shorSiteEquiv rows columns
  change (∏ s, pauliParitySign (zBit (p s) * a (e s))) =
    ∏ ij, pauliParitySign (zBit (p (e.symm ij)) * a ij)
  calc
    (∏ s, pauliParitySign (zBit (p s) * a (e s))) =
        ∏ s, pauliParitySign (zBit (p (e.symm (e s))) * a (e s)) := by
      apply Finset.prod_congr rfl
      intro s _
      have hs : e.symm (e s) = s := e.symm_apply_apply s
      rw [hs]
    _ = ∏ ij, pauliParitySign (zBit (p (e.symm ij)) * a ij) :=
      e.prod_comp (fun ij => pauliParitySign (zBit (p (e.symm ij)) * a ij))

theorem physicalZ_commutation (a : Mask rows columns) (p : Fin (rows * columns) → SinglePauli) :
    pauliMatrix 0 (physicalZWord a) * pauliMatrix 0 p =
      pauliParitySign (maskDot (xMaskOfPauli p) a) •
        (pauliMatrix 0 p * pauliMatrix 0 (physicalZWord a)) := by
  rw [unphased_pauliMatrix_commutation]
  congr 1
  unfold maskDot
  rw [paritySign_sum]
  simp only [physicalZWord, singleZ_commutation, xMaskOfPauli]
  let e := shorSiteEquiv rows columns
  change (∏ s, pauliParitySign (xBit (p s) * a (e s))) =
    ∏ ij, pauliParitySign (xBit (p (e.symm ij)) * a ij)
  calc
    (∏ s, pauliParitySign (xBit (p s) * a (e s))) =
        ∏ s, pauliParitySign (xBit (p (e.symm (e s))) * a (e s)) := by
      apply Finset.prod_congr rfl
      intro s _
      have hs : e.symm (e s) = s := e.symm_apply_apply s
      rw [hs]
    _ = ∏ ij, pauliParitySign (xBit (p (e.symm ij)) * a ij) :=
      e.prod_comp (fun ij => pauliParitySign (xBit (p (e.symm ij)) * a ij))

private theorem singlePauli_eq_XZ (p : SinglePauli) :
    p.matrix = (if p = .Y then Complex.I else 1) •
      ((if xBit p = 0 then SinglePauli.I else SinglePauli.X).matrix *
        (if zBit p = 0 then SinglePauli.I else SinglePauli.Z).matrix) := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [xBit, zBit, SinglePauli.matrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul, Complex.I_mul_I]

theorem pauliMatrix_eq_physicalXZ (p : Fin (rows * columns) → SinglePauli) :
    pauliMatrix 0 p = (∏ s, if p s = .Y then Complex.I else 1) •
      (pauliMatrix 0 (physicalXWord (xMaskOfPauli p)) *
        pauliMatrix 0 (physicalZWord (zMaskOfPauli p))) := by
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul, ← tensorEntries_smul]
  congr 1
  funext s
  simpa only [physicalXWord, physicalZWord, xMaskOfPauli, zMaskOfPauli, Equiv.symm_apply_apply]
    using singlePauli_eq_XZ (p s)

#print axioms pauliSupport_card_eq_rectangular
#print axioms physicalX_commutation
#print axioms physicalZ_commutation
#print axioms pauliMatrix_eq_physicalXZ

end CriticalDepth.FaultShorSaturation
