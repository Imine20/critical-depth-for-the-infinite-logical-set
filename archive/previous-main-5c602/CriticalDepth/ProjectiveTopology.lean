import CriticalDepth.ProjectiveFaithfulness
import CriticalDepth.Rotations
import CriticalDepth.ManuscriptStatements
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Maps.Basic

/-!
# The actual projective unitary space and non-density

The carrier is the quotient of genuine unitary matrices by one global phase,
with the standard quotient topology inherited from the matrix topology.
Closed fibers of the continuous conjugation-coordinate map prove the T1
property. Infinitude is witnessed by genuine unitary rational rotations.
No nonunitary matrix or zero matrix is used to establish non-density.
-/

noncomputable section

namespace CriticalDepth

open Matrix

universe u

abbrev UnitaryOperator (ι : Type u) [Fintype ι] [DecidableEq ι] :=
  {U : Operator ι // IsUnitary U}

def unitaryPhaseSetoid (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Setoid (UnitaryOperator ι) where
  r U V := ProjectivelyEquivalent U.val V.val
  iseqv := ⟨fun U => projectivelyEquivalent_refl U.val,
    fun h => projectivelyEquivalent_symm h,
    fun h₁ h₂ => projectivelyEquivalent_trans h₁ h₂⟩

/-- Genuine projective unitaries, equipped with the usual quotient topology. -/
abbrev ProjectiveUnitary (ι : Type u) [Fintype ι] [DecidableEq ι] :=
  Quotient (unitaryPhaseSetoid ι)

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def unitaryProjectiveClass (U : UnitaryOperator ι) : ProjectiveUnitary ι :=
  Quotient.mk (unitaryPhaseSetoid ι) U

/-- Forget unitarity while retaining exactly the same global-phase class. -/
def projectiveUnitaryToOperator (ι : Type u) [Fintype ι] [DecidableEq ι] :
    ProjectiveUnitary ι → ProjectiveOperator ι :=
  Quotient.lift (fun U : UnitaryOperator ι => projectiveClass U.val)
    (fun _ _ h => Quotient.sound h)

@[simp] theorem projectiveUnitaryToOperator_mk (U : UnitaryOperator ι) :
    projectiveUnitaryToOperator ι (unitaryProjectiveClass U) = projectiveClass U.val := rfl

theorem projectiveUnitaryToOperator_injective :
    Function.Injective (projectiveUnitaryToOperator ι) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro U V h
  change projectiveClass U.val = projectiveClass V.val at h
  have hphase :=
    @Quotient.exact (Operator ι) (projectiveSetoid ι) U.val V.val h
  exact @Quotient.sound (UnitaryOperator ι) (unitaryPhaseSetoid ι) U V hphase

theorem continuous_conjugationCoordinates :
    Continuous (conjugationCoordinates : Operator ι → Operator (ι × ι)) := by
  unfold conjugationCoordinates
  fun_prop

theorem continuous_unitaryConjugationCoordinates :
    Continuous (fun U : UnitaryOperator ι => conjugationCoordinates U.val) :=
  continuous_conjugationCoordinates.comp continuous_subtype_val

theorem isClosed_unitary_phase_fiber [Nonempty ι] (U : UnitaryOperator ι) :
    IsClosed {V : UnitaryOperator ι | ProjectivelyEquivalent V.val U.val} := by
  have heq : {V : UnitaryOperator ι | ProjectivelyEquivalent V.val U.val} =
      (fun V : UnitaryOperator ι => conjugationCoordinates V.val) ⁻¹'
        {conjugationCoordinates U.val} := by
    ext V
    change ProjectivelyEquivalent V.val U.val ↔
      conjugationCoordinates V.val = conjugationCoordinates U.val
    exact (unitary_conjugationCoordinates_eq_iff_projectivelyEquivalent
      V.val U.val V.property U.property).symm
  rw [heq]
  exact isClosed_singleton.preimage continuous_unitaryConjugationCoordinates

theorem unitaryProjectiveClass_singleton_preimage (U : UnitaryOperator ι) :
    unitaryProjectiveClass ⁻¹' {unitaryProjectiveClass U} =
      {V : UnitaryOperator ι | ProjectivelyEquivalent V.val U.val} := by
  ext V
  change unitaryProjectiveClass V = unitaryProjectiveClass U ↔
    ProjectivelyEquivalent V.val U.val
  constructor
  · intro h
    exact @Quotient.exact (UnitaryOperator ι) (unitaryPhaseSetoid ι) V U h
  · intro h
    exact @Quotient.sound (UnitaryOperator ι) (unitaryPhaseSetoid ι) V U h

/-- Projective unitary singletons are closed because their quotient
preimages are closed conjugation-coordinate fibers. -/
instance projectiveUnitaryT1Space [Nonempty ι] : T1Space (ProjectiveUnitary ι) where
  t1 q := by
    refine Quotient.inductionOn q ?_
    intro U
    letI : Setoid (UnitaryOperator ι) := unitaryPhaseSetoid ι
    have hquot : Topology.IsQuotientMap
        (Quotient.mk' : UnitaryOperator ι → ProjectiveUnitary ι) :=
      isQuotientMap_quotient_mk'
    apply ((Topology.isQuotientMap_iff_isClosed.mp hquot).2
      ({unitaryProjectiveClass U} : Set (ProjectiveUnitary ι))).mpr
    change IsClosed (unitaryProjectiveClass ⁻¹' {unitaryProjectiveClass U})
    rw [unitaryProjectiveClass_singleton_preimage]
    exact isClosed_unitary_phase_fiber U

def signInvolution (K : ℕ) : Operator (Fin K) :=
  fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0

theorem signInvolution_selfAdjoint (K : ℕ) : star (signInvolution K) = signInvolution K := by
  classical
  ext i j
  change star (signInvolution K j i) = signInvolution K i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = 0 <;> simp [signInvolution, hi]
  · simp [signInvolution, hij, Ne.symm hij]

theorem signInvolution_sq (K : ℕ) : signInvolution K * signInvolution K = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = 0 <;>
      simp [signInvolution, Matrix.mul_apply, Matrix.one_apply, hi]
  · simp [signInvolution, Matrix.mul_apply, Matrix.one_apply, hij]

theorem signInvolution_not_isScalar (K : ℕ) (hK : 2 ≤ K) : ¬ IsScalar (signInvolution K) := by
  intro h
  obtain ⟨z, hz⟩ := h
  let i₀ : Fin K := ⟨0, by omega⟩
  let i₁ : Fin K := ⟨1, by omega⟩
  have h₀ : (1 : ℂ) = z := by
    have heq := congrArg (fun A : Operator (Fin K) => A i₀ i₀) hz
    simpa [signInvolution, i₀] using heq
  have h₁ : (-1 : ℂ) = z := by
    have heq := congrArg (fun A : Operator (Fin K) => A i₁ i₁) hz
    simpa [signInvolution, i₁] using heq
  have hbad : (1 : ℂ) = -1 := h₀.trans h₁.symm
  norm_num at hbad

def rationalRotationUnitary (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) (r : ℕ) : UnitaryOperator ι :=
  ⟨rationalRotation P r, rationalRotation_isUnitary hself hsq r⟩

theorem rationalRotation_projectiveUnitary_injective
    (P : Operator ι) (hself : star P = P) (hsq : P * P = 1) (hP : ¬ IsScalar P) :
    Function.Injective (fun r : ℕ =>
      unitaryProjectiveClass (rationalRotationUnitary P hself hsq r)) := by
  intro r s hrs
  have heq := congrArg (projectiveUnitaryToOperator ι) hrs
  change projectiveClass (rationalRotation P r) =
    projectiveClass (rationalRotation P s) at heq
  exact rationalRotation_classes_injective hP heq

/-- Infinitude is witnessed inside the unitary carrier itself. -/
theorem projectiveUnitary_infinite (K : ℕ) (hK : 2 ≤ K) :
    Infinite (ProjectiveUnitary (Fin K)) := by
  exact Infinite.of_injective _
    (rationalRotation_projectiveUnitary_injective (signInvolution K)
      (signInvolution_selfAdjoint K) (signInvolution_sq K)
      (signInvolution_not_isScalar K hK))

theorem finite_projectiveUnitary_preimage
    (S : Set (ProjectiveOperator ι)) (hS : S.Finite) :
    (projectiveUnitaryToOperator ι ⁻¹' S).Finite :=
  Set.Finite.preimage (projectiveUnitaryToOperator_injective (ι := ι)).injOn hS

/-- A finite projective image is not dense in the actual projective unitary
space in dimension at least two. -/
theorem finite_projectiveImage_not_dense_in_projectiveUnitary
    (K : ℕ) (hK : 2 ≤ K) (S : Set (ProjectiveOperator (Fin K))) (hS : S.Finite) :
    ¬ Dense (projectiveUnitaryToOperator (Fin K) ⁻¹' S) := by
  letI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  letI : Infinite (ProjectiveUnitary (Fin K)) := projectiveUnitary_infinite K hK
  have hfinite := finite_projectiveUnitary_preimage S hS
  intro hdense
  have heq : projectiveUnitaryToOperator (Fin K) ⁻¹' S = Set.univ :=
    hfinite.isClosed.closure_eq.symm.trans hdense.closure_eq
  have huniv : (Set.univ : Set (ProjectiveUnitary (Fin K))).Finite := by
    rw [← heq]
    exact hfinite
  exact Set.infinite_univ huniv

namespace Manuscript

/-- Every logical action in the manuscript's image has a genuinely unitary
representative, hence belongs to the image of the projective unitary carrier. -/
theorem logicalImage_subset_projectiveUnitary_range
    {n ℓ g q h : ℕ} {dim : Fin n → ℕ} (C : Code n dim ℓ g) :
    logicalImage C q h ⊆ Set.range (projectiveUnitaryToOperator (Fin ℓ)) := by
  rintro a ⟨c, W, hW, rfl⟩
  exact ⟨unitaryProjectiveClass ⟨W, hW.1⟩, rfl⟩

/-- The non-density corollary of Theorem 1, expressed in the quotient of
unitaries rather than in the quotient of all matrices. -/
theorem logicalImage_not_dense_in_projectiveUnitary
    {n ℓ g q h : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim ℓ g) (hℓ : 2 ≤ ℓ) (hfinite : (logicalImage C q h).Finite) :
    ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' logicalImage C q h) :=
  finite_projectiveImage_not_dense_in_projectiveUnitary ℓ hℓ _ hfinite

end Manuscript

end CriticalDepth
