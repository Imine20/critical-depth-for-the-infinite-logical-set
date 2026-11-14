import CSSExhaustiveSelection

/-!
The exhaustive CSS selection with the planted word prescribed in advance.
The candidate order is the same finite lexicographic enumeration.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped Matrix

def CSSPlantedBasisPasses (R : ℕ) (p : CSSWord (cssSites R)) (C : CSSBasisCandidates R) : Prop :=
  CSSReducedBasisPasses R C ∧
    ∀ a : Fin (cssXDimension R) → CSSBit, dotProduct p (a ᵥ* C.1) = 0

instance cssPlantedBasisPasses_decidable (R : ℕ) (p : CSSWord (cssSites R))
    (C : CSSBasisCandidates R) : Decidable (CSSPlantedBasisPasses R p C) := by
  unfold CSSPlantedBasisPasses
  exact @instDecidableAnd _ _ (cssReducedBasisPasses_decidable R C)
    (@Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance)

theorem cssPlantedBasisPasses_iff (R : ℕ) (p : CSSWord (cssSites R)) (C : CSSBasisCandidates R) :
    CSSPlantedBasisPasses R p C ↔
      CSSReducedBasisPasses R C ∧ p ∈ cssOrthogonal C.1.vecMulLinear.range := by
  unfold CSSPlantedBasisPasses
  apply and_congr_right'
  rw [cssOrthogonal_mem]
  constructor
  · rintro h _ ⟨a, rfl⟩
    exact h a
  · intro h a
    exact h (a ᵥ* C.1) ⟨a, rfl⟩

theorem exists_cssPlantedBasisPasses (R : ℕ) (hR : 2 ^ 20 ≤ R)
    (p : CSSWord (cssSites R)) (hp : wordWeight p = cssDistance R) :
    ∃ C : CSSBasisCandidates R, CSSPlantedBasisPasses R p C := by
  obtain ⟨H, J, hRigid, hH, hJ, hPlanted, hDual⟩ :=
    exists_rigid_checkSpaces_for_planted R hR p hp
  obtain ⟨C, hA, hB, hC, hRange, _⟩ :=
    exists_cssBasisPasses_of_checkSpaces R H J p hRigid hH hJ hPlanted hp hDual
  refine ⟨C, (cssPlantedBasisPasses_iff R p C).mpr ⟨⟨hA, hB, hC⟩, ?_⟩⟩
  rwa [hRange]

def firstPassingPlantedCSSIndex (R N : ℕ) (enumerate : Fin N → CSSBasisCandidates R)
    (p : CSSWord (cssSites R)) : WithTop (Fin N) :=
  (Finset.univ.filter fun i => CSSPlantedBasisPasses R p (enumerate i)).min

theorem firstPassingPlantedCSSIndex_spec (R N : ℕ) (enumerate : Fin N ≃ CSSBasisCandidates R)
    (hR : 2 ^ 20 ≤ R) (p : CSSWord (cssSites R)) (hp : wordWeight p = cssDistance R) :
    ∃ i : Fin N, firstPassingPlantedCSSIndex R N enumerate p = i ∧
      CSSPlantedBasisPasses R p (enumerate i) ∧
      ∀ j, CSSPlantedBasisPasses R p (enumerate j) → i ≤ j := by
  let S := Finset.univ.filter fun i : Fin N => CSSPlantedBasisPasses R p (enumerate i)
  obtain ⟨C, hC⟩ := exists_cssPlantedBasisPasses R hR p hp
  obtain ⟨j, rfl⟩ := enumerate.surjective C
  obtain ⟨i, hi⟩ := Finset.min_of_nonempty (show S.Nonempty from
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩⟩)
  refine ⟨i, hi, (Finset.mem_filter.mp (Finset.mem_of_min hi)).2, fun k hk => ?_⟩
  exact Finset.min_le_of_eq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hi

/-- The first lexicographic pair of certified row-reduced bases for the
designated planted word. -/
def exhaustivePlantedCSSBasis (R : ℕ) (p : CSSWord (cssSites R)) : Option (CSSBasisCandidates R) :=
  (firstPassingPlantedCSSIndex R _ (cssBasisEnumeration R) p).map (cssBasisEnumeration R)

theorem exhaustivePlantedCSSBasis_exists (R : ℕ) (hR : 2 ^ 20 ≤ R)
    (p : CSSWord (cssSites R)) (hp : wordWeight p = cssDistance R) :
    ∃ C, exhaustivePlantedCSSBasis R p = some C ∧ CSSPlantedBasisPasses R p C := by
  obtain ⟨i, he, hPass, _⟩ := firstPassingPlantedCSSIndex_spec R _ (cssBasisEnumeration R) hR p hp
  refine ⟨cssBasisEnumeration R i, ?_, hPass⟩
  change WithTop.map (cssBasisEnumeration R)
      (firstPassingPlantedCSSIndex R _ (cssBasisEnumeration R) p) =
    (↑(cssBasisEnumeration R i) : WithTop (CSSBasisCandidates R))
  exact (congrArg (WithTop.map (cssBasisEnumeration R)) he).trans (WithTop.map_coe _ _)

#print axioms exhaustivePlantedCSSBasis
#print axioms exhaustivePlantedCSSBasis_exists
#print axioms firstPassingPlantedCSSIndex_spec

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
