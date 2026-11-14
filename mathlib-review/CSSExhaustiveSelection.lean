import CSSRandomRigidity
import CSSReducedRowBasis
import Mathlib.Data.Finset.Max
import Mathlib.Data.FinEnum

/-!
Finite exhaustive search for CSS check matrices. The search order is supplied
as a bijective numbering, so the implementation can use a chosen lexicographic
numbering. The finite predicates test binary words and matrices directly.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

abbrev CSSBasisCandidates (R : ℕ) :=
  Matrix (Fin (cssXDimension R)) (Fin (cssSites R)) CSSBit ×
  Matrix (Fin (cssZDimension R)) (Fin (cssSites R)) CSSBit

private def certWeight {n : ℕ} (x : BW n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

private theorem certWeight_eq {n : ℕ} (x : BW n) : certWeight x = wordWeight x := by
  classical
  unfold certWeight wordWeight
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private def RowMember {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (x : BW n) : Prop :=
  ∃ t : Fin k → CSSBit, t ᵥ* A = x

private def RowOrthogonal {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (x : BW n) : Prop :=
  ∀ t : Fin k → CSSBit, dotProduct x (t ᵥ* A) = 0

private instance {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (x : BW n) :
    Decidable (RowMember A x) := by unfold RowMember; infer_instance

private instance {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (x : BW n) :
    Decidable (RowOrthogonal A x) := by unfold RowOrthogonal; infer_instance

private theorem rowMember_iff_range {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (x : BW n) :
    RowMember A x ↔ x ∈ A.vecMulLinear.range := Iff.rfl

private theorem rowOrthogonal_iff {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (x : BW n) :
    RowOrthogonal A x ↔ x ∈ cssOrthogonal A.vecMulLinear.range := by
  rw [cssOrthogonal_mem]
  constructor
  · rintro h _ ⟨t, rfl⟩
    exact h t
  · exact fun h t => h (t ᵥ* A) ⟨t, rfl⟩

private def LinearCandidate {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (R : ℕ)
    (F : Matrix (Fin n) (Fin n) CSSBit) : Prop :=
  (∀ x y : BW n, F *ᵥ x = F *ᵥ y → x = y) ∧
  (∀ y : BW n, ∃ x : BW n, F *ᵥ x = y) ∧
  (∀ i, certWeight (F.row i) ≤ R) ∧ (∀ j, certWeight (F.col j) ≤ R) ∧
  (∀ x : BW n, RowMember A x ↔ ∃ y : BW n, RowMember A y ∧ F *ᵥ y = x)

private instance {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (R : ℕ)
    (F : Matrix (Fin n) (Fin n) CSSBit) : Decidable (LinearCandidate A R F) := by
  unfold LinearCandidate
  infer_instance

private theorem linearCandidate_iff {k n : ℕ} (A : Matrix (Fin k) (Fin n) CSSBit) (R : ℕ)
    (F : Matrix (Fin n) (Fin n) CSSBit) :
    LinearCandidate A R F ↔ SparseLinearPreserver A.vecMulLinear.range R F := by
  unfold LinearCandidate SparseLinearPreserver
  simp only [certWeight_eq, rowMember_iff_range, Function.Bijective,
    Function.Injective, Function.Surjective, Matrix.row, Matrix.col]
  constructor
  · rintro ⟨hi, hs, hr, hc, h⟩
    refine ⟨⟨hi, hs⟩, hr, hc, ?_⟩
    ext x
    exact (h x).symm
  · rintro ⟨⟨hi, hs⟩, hr, hc, h⟩
    refine ⟨hi, hs, hr, hc, ?_⟩
    intro x
    change x ∈ (A.vecMulLinear.range : Set (BW n)) ↔
      x ∈ F.mulVec '' (A.vecMulLinear.range : Set (BW n))
    rw [h]

/-- A finite check on ordered row bases for the same rigidity certificate as
the CSS existence theorem. All quantified variables range over binary matrices
or words of specified finite length. -/
def CSSBasisPasses (R : ℕ) (C : CSSBasisCandidates R) : Prop :=
  (∀ s t : Fin (cssXDimension R) → CSSBit, s ᵥ* C.1 = t ᵥ* C.1 → s = t) ∧
  (∀ s t : Fin (cssZDimension R) → CSSBit, s ᵥ* C.2 = t ᵥ* C.2 → s = t) ∧
  (∀ x, RowMember C.1 x → RowOrthogonal C.2 x) ∧
  (∃ p, RowOrthogonal C.1 p ∧ certWeight p = cssDistance R) ∧
  (∀ x, RowOrthogonal C.1 x → x ≠ 0 → cssDistance R ≤ certWeight x) ∧
  (∀ x, RowOrthogonal C.2 x → x ≠ 0 →
    R * (cssXDimension R + 1) < certWeight x) ∧
  (∀ x, RowMember C.2 x → x ≠ 0 → cssDeletionThreshold R < certWeight x) ∧
  (∀ F, LinearCandidate C.1 R F → F = 1) ∧
  (∀ Q : Matrix (Fin (cssSites R)) (Fin (cssSites R)) CSSBit,
    Q.transpose = Q → (∀ i, certWeight (Q.row i) ≤ R + 1) →
    (∀ x, RowMember C.1 x → RowMember C.2 (Q *ᵥ x)) → Q = 0)

instance cssBasisPasses_decidable (R : ℕ) (C : CSSBasisCandidates R) :
    Decidable (CSSBasisPasses R C) := by
  let hX : Decidable (∀ s t : Fin (cssXDimension R) → CSSBit,
      s ᵥ* C.1 = t ᵥ* C.1 → s = t) :=
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
  let hZ : Decidable (∀ s t : Fin (cssZDimension R) → CSSBit,
      s ᵥ* C.2 = t ᵥ* C.2 → s = t) :=
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
  let hCompatible : Decidable (∀ x, RowMember C.1 x → RowOrthogonal C.2 x) :=
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
  let hPlanted : Decidable (∃ p, RowOrthogonal C.1 p ∧ certWeight p = cssDistance R) :=
    @Fintype.decidableExistsFintype _ _ (fun _ => inferInstance) inferInstance
  let hXDist : Decidable (∀ x, RowOrthogonal C.1 x → x ≠ 0 → cssDistance R ≤ certWeight x) :=
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
  let hZDist : Decidable (∀ x, RowOrthogonal C.2 x → x ≠ 0 →
      R * (cssXDimension R + 1) < certWeight x) :=
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
  let hZPrimal : Decidable (∀ x, RowMember C.2 x → x ≠ 0 →
      cssDeletionThreshold R < certWeight x) :=
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
  let hLinear : Decidable (∀ F, LinearCandidate C.1 R F → F = 1) :=
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
  let hSymmetric : Decidable (∀ Q : Matrix (Fin (cssSites R)) (Fin (cssSites R)) CSSBit,
      Q.transpose = Q → (∀ i, certWeight (Q.row i) ≤ R + 1) →
      (∀ x, RowMember C.1 x → RowMember C.2 (Q *ᵥ x)) → Q = 0) :=
    @Fintype.decidableForallFintype _ _ (fun Q => by
      letI : Decidable (∀ i, certWeight (Q.row i) ≤ R + 1) :=
        @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
      letI : Decidable (∀ x, RowMember C.1 x → RowMember C.2 (Q *ᵥ x)) :=
        @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) inferInstance
      infer_instance) inferInstance
  exact @instDecidableAnd _ _ hX (@instDecidableAnd _ _ hZ
    (@instDecidableAnd _ _ hCompatible (@instDecidableAnd _ _ hPlanted
    (@instDecidableAnd _ _ hXDist (@instDecidableAnd _ _ hZDist
    (@instDecidableAnd _ _ hZPrimal (@instDecidableAnd _ _ hLinear hSymmetric)))))))

private theorem finrank_rowRange_eq_of_injective {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) CSSBit)
    (hA : Function.Injective A.vecMulLinear) :
    Module.finrank CSSBit A.vecMulLinear.range = k := by
  rw [LinearMap.finrank_range_of_inj hA, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem rigidity_of_cssBasisPasses (R : ℕ) (hR : 2 ≤ R)
    (C : CSSBasisCandidates R) (h : CSSBasisPasses R C) :
    let H := C.1.vecMulLinear.range
    let J := C.2.vecMulLinear.range
    RigidityCheckSpaces H J R ∧ Module.finrank CSSBit H = cssXDimension R ∧
      Module.finrank CSSBit J = cssZDimension R ∧
      (∃ p ∈ cssOrthogonal H, wordWeight p = cssDistance R) ∧
      ∀ x ∈ cssOrthogonal H, x ≠ 0 → cssDistance R ≤ wordWeight x := by
  obtain ⟨hA, hB, hCompat, hP, hX, hZ, hPrimal, hLinear, hSymm⟩ := h
  let H := C.1.vecMulLinear.range
  let J := C.2.vecMulLinear.range
  have ha : Module.finrank CSSBit H = cssXDimension R :=
    finrank_rowRange_eq_of_injective C.1 hA
  have hb : Module.finrank CSSBit J = cssZDimension R :=
    finrank_rowRange_eq_of_injective C.2 hB
  have hx (x : BW (cssSites R)) (hh : x ∈ cssOrthogonal H) (hne : x ≠ 0) :
      cssDistance R ≤ wordWeight x := by
    rw [← certWeight_eq]
    exact hX x ((rowOrthogonal_iff C.1 x).mpr hh) hne
  refine ⟨?_, ha, hb, ?_, hx⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact (rowOrthogonal_iff _ _).mp (hCompat x hx)
    · rw [ha]
      exact cssXDimension_le_sites R (by omega)
    · rw [ha, hb]
      exact css_logicalDimension_positive R hR
    · exact fun x hh hn => (cssDistance_gt_localBound R hR).trans_le (hx x hh hn)
    · intro x hh hn
      rw [ha, ← certWeight_eq]
      exact hZ x ((rowOrthogonal_iff C.2 x).mpr hh) hn
    · intro x hh hn
      rw [ha, hb, ← certWeight_eq]
      exact hPrimal x hh hn
    · exact fun F hF => hLinear F ((linearCandidate_iff _ _ _).mpr hF)
    · intro Q hQ hw hmap
      exact hSymm Q hQ (fun i => (certWeight_eq _).trans_le (hw i)) hmap
  · obtain ⟨p, hp, hpw⟩ := hP
    exact ⟨p, (rowOrthogonal_iff _ _).mp hp, (certWeight_eq _).symm.trans hpw⟩

theorem exists_cssBasisPasses_of_checkSpaces (R : ℕ)
    (H J : Submodule CSSBit (CSSWord (cssSites R))) (p : CSSWord (cssSites R))
    (hRigid : RigidityCheckSpaces H J R)
    (hH : Module.finrank CSSBit H = cssXDimension R)
    (hJ : Module.finrank CSSBit J = cssZDimension R)
    (hp : p ∈ cssOrthogonal H) (hpw : wordWeight p = cssDistance R)
    (hd : ∀ x ∈ cssOrthogonal H, x ≠ 0 → cssDistance R ≤ wordWeight x) :
    ∃ C : CSSBasisCandidates R, BinaryRREF C.1 ∧ BinaryRREF C.2 ∧ CSSBasisPasses R C ∧
      C.1.vecMulLinear.range = H ∧ C.2.vecMulLinear.range = J := by
  obtain ⟨A, hArr, hA, hAr⟩ := exists_binaryRREF_matrix H hH
  obtain ⟨B, hBrr, hB, hBr⟩ := exists_binaryRREF_matrix J hJ
  refine ⟨(A, B), hArr, hBrr, ?_, hAr, hBr⟩
  refine ⟨hA, hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [rowOrthogonal_iff, hBr]
    rw [rowMember_iff_range, hAr] at hx
    exact hRigid.compatible hx
  · refine ⟨p, ?_, (certWeight_eq _).trans hpw⟩
    rwa [rowOrthogonal_iff, hAr]
  · intro x hx hn
    rw [rowOrthogonal_iff, hAr] at hx
    rw [certWeight_eq]
    exact hd x hx hn
  · intro x hx hn
    rw [rowOrthogonal_iff, hBr] at hx
    rw [certWeight_eq, ← hH]
    exact hRigid.zDualDistance x hx hn
  · intro x hx hn
    rw [rowMember_iff_range, hBr] at hx
    rw [certWeight_eq]
    simpa only [cssDeletionThreshold, hH, hJ] using hRigid.zDistance x hx hn
  · intro F hF
    rw [linearCandidate_iff, hAr] at hF
    exact hRigid.linearExclusion F hF
  · intro Q hQ hRow hMap
    apply hRigid.symmetricExclusion Q hQ
    · exact fun i => (certWeight_eq _).symm.trans_le (hRow i)
    · intro x hx
      change Q *ᵥ x ∈ J
      rw [← hBr, ← rowMember_iff_range]
      apply hMap
      rwa [rowMember_iff_range, hAr]

theorem exists_cssBasisPasses (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    ∃ C : CSSBasisCandidates R, BinaryRREF C.1 ∧ BinaryRREF C.2 ∧ CSSBasisPasses R C := by
  obtain ⟨H, J, p, hRigid, hH, hJ, hp, hpw, hd⟩ := exists_rigid_checkSpaces R hR
  obtain ⟨C, hA, hB, hC, _, _⟩ := exists_cssBasisPasses_of_checkSpaces R H J p hRigid hH hJ hp hpw hd
  exact ⟨C, hA, hB, hC⟩

/-- Only pairs of reduced row-echelon matrices enter the finite search. -/
def CSSReducedBasisPasses (R : ℕ) (C : CSSBasisCandidates R) : Prop :=
  BinaryRREF C.1 ∧ BinaryRREF C.2 ∧ CSSBasisPasses R C

instance cssReducedBasisPasses_decidable (R : ℕ) (C : CSSBasisCandidates R) :
    Decidable (CSSReducedBasisPasses R C) := by
  unfold CSSReducedBasisPasses
  infer_instance

/-- The result is the first passing candidate in the supplied finite order.
All definitions in the search use executable finite instances. -/
def firstPassingCSSIndex (R N : ℕ) (enumerate : Fin N → CSSBasisCandidates R) : WithTop (Fin N) :=
  (Finset.univ.filter fun i => CSSReducedBasisPasses R (enumerate i)).min

theorem firstPassingCSSIndex_spec (R N : ℕ) (enumerate : Fin N ≃ CSSBasisCandidates R)
    (hR : 2 ^ 20 ≤ R) :
    ∃ i : Fin N, firstPassingCSSIndex R N enumerate = i ∧
      CSSReducedBasisPasses R (enumerate i) ∧
      ∀ j, CSSReducedBasisPasses R (enumerate j) → i ≤ j := by
  let S := Finset.univ.filter fun i : Fin N => CSSReducedBasisPasses R (enumerate i)
  obtain ⟨C, hC⟩ := exists_cssBasisPasses R hR
  obtain ⟨j, rfl⟩ := enumerate.surjective C
  obtain ⟨i, hi⟩ := Finset.min_of_nonempty (show S.Nonempty from
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩⟩)
  refine ⟨i, hi, (Finset.mem_filter.mp (Finset.mem_of_min hi)).2, fun k hk => ?_⟩
  exact Finset.min_le_of_eq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hi

local instance : FinEnum CSSBit :=
  FinEnum.ofEquiv (Fin 2) (ZMod.finEquiv 2).toEquiv.symm

local instance {k n : ℕ} : FinEnum (Matrix (Fin k) (Fin n) CSSBit) :=
  FinEnum.ofEquiv (Fin k → Fin n → CSSBit) (by
    change (Fin k → Fin n → CSSBit) ≃ (Fin k → Fin n → CSSBit)
    exact Equiv.refl _)

/-- The concrete order is the nested finite enumeration with increasing row and
column coordinates and binary values ordered zero before one. -/
def cssBasisEnumeration (R : ℕ) :
    Fin (FinEnum.card (CSSBasisCandidates R)) ≃ CSSBasisCandidates R :=
  (FinEnum.equiv (α := CSSBasisCandidates R)).symm

/-- A finite index denotes the first passing pair of reduced row-echelon bases. -/
def exhaustiveCSSBasis (R : ℕ) : Option (CSSBasisCandidates R) :=
  (firstPassingCSSIndex R (FinEnum.card (CSSBasisCandidates R)) (cssBasisEnumeration R)).map
    (cssBasisEnumeration R)

theorem exhaustiveCSSBasis_exists (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    ∃ C, exhaustiveCSSBasis R = some C ∧ CSSReducedBasisPasses R C := by
  obtain ⟨i, he, hPass, _⟩ := firstPassingCSSIndex_spec R _ (cssBasisEnumeration R) hR
  refine ⟨cssBasisEnumeration R i, ?_, hPass⟩
  unfold exhaustiveCSSBasis
  rw [he] <;> rfl

#print axioms exhaustiveCSSBasis
#print axioms exhaustiveCSSBasis_exists

#print axioms rigidity_of_cssBasisPasses
#print axioms exists_cssBasisPasses_of_checkSpaces
#print axioms exists_cssBasisPasses
#print axioms firstPassingCSSIndex_spec

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
