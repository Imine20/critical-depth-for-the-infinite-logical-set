import CriticalDepth.MatrixCore

/-!
# Faithfulness of conjugation modulo one global phase

The quantified conjugation test uses every complex matrix. Its equivalent
coordinate matrix is an explicit finite array, so finiteness of this array's
image transfers to the manuscript's actual global-phase quotient.
-/

noncomputable section

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixUnit (j k : ι) : Operator ι :=
  fun a b => if a = j ∧ b = k then 1 else 0

theorem scalar_of_commutes_matrixUnits [Nonempty ι]
    (T : Operator ι)
    (hcomm : ∀ j k : ι, T * matrixUnit j k = matrixUnit j k * T) : IsScalar T := by
  classical
  let k : ι := Classical.choice inferInstance
  refine ⟨T k k, ?_⟩
  ext i j
  have hh := congrArg (fun A : Operator ι => A i k) (hcomm j k)
  by_cases hij : i = j
  · subst j
    simpa [matrixUnit, Matrix.mul_apply, Matrix.one_apply, mul_ite, ite_mul] using hh
  · simpa [matrixUnit, Matrix.mul_apply, Matrix.one_apply, hij, mul_ite, ite_mul] using hh

theorem scalar_of_commutes_all [Nonempty ι]
    (T : Operator ι) (hcomm : ∀ M : Operator ι, T * M = M * T) : IsScalar T := by
  apply scalar_of_commutes_matrixUnits T
  intro j k
  exact hcomm (matrixUnit j k)

theorem unitary_smul_phase [Nonempty ι]
    {U V : Operator ι} {z : ℂ} (hU : IsUnitary U) (hV : IsUnitary V)
    (hUV : U = z • V) : star z * z = 1 := by
  classical
  have hu := hU.1
  rw [hUV] at hu
  have hnorm : (star z * z) • (1 : Operator ι) = 1 := by
    simpa [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hV.1, mul_comm] using hu
  let i : ι := Classical.choice inferInstance
  have hdiag := congrArg (fun A : Operator ι => A i i) hnorm
  simpa using hdiag

def conjugation (U M : Operator ι) : Operator ι := U * M * star U

theorem projectivelyEquivalent_conjugation_eq
    {U V : Operator ι} (h : ProjectivelyEquivalent U V) (M : Operator ι) :
    conjugation U M = conjugation V M := by
  obtain ⟨z, hz, rfl⟩ := h
  simp only [conjugation, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  change (star z * z) • (V * M * star V) = V * M * star V
  rw [hz, one_smul]

theorem unitary_conjugation_eq_iff_projectivelyEquivalent [Nonempty ι]
    (U V : Operator ι) (hU : IsUnitary U) (hV : IsUnitary V) :
    (∀ M : Operator ι, conjugation U M = conjugation V M) ↔
      ProjectivelyEquivalent U V := by
  constructor
  · intro hconj
    let T : Operator ι := star V * U
    have hcomm : ∀ M : Operator ι, T * M = M * T := by
      intro M
      calc
        T * M = star V * (U * M * star U) * U := by
          simp only [T, Matrix.mul_assoc, hU.1, mul_one]
        _ = star V * (V * M * star V) * U := by
          rw [show U * M * star U = V * M * star V from hconj M]
        _ = M * T := by
          simp only [T, ← Matrix.mul_assoc, hV.1, one_mul]
    obtain ⟨z, hT⟩ := scalar_of_commutes_all T hcomm
    have hUV : U = z • V := by
      calc
        U = (V * star V) * U := by rw [hV.2]; simp
        _ = V * (star V * U) := by rw [Matrix.mul_assoc]
        _ = V * T := rfl
        _ = V * (z • (1 : Operator ι)) := by rw [hT]
        _ = z • V := by simp [mul_smul_comm]
    exact ⟨z, unitary_smul_phase hU hV hUV, hUV⟩
  · intro h M
    exact projectivelyEquivalent_conjugation_eq h M

/-- The matrix of conjugation on matrix units, with output and input index pairs. -/
def conjugationCoordinates (U : Operator ι) : Operator (ι × ι) :=
  fun p r => U p.1 r.1 * (star U) r.2 p.2

theorem conjugationCoordinates_eq_iff
    (U V : Operator ι) : conjugationCoordinates U = conjugationCoordinates V ↔
      ∀ M : Operator ι, conjugation U M = conjugation V M := by
  classical
  constructor
  · intro hc M
    ext i k
    simp only [conjugation, Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    have hh := congrArg (fun A : Operator (ι × ι) => A (i, k) (j, l)) hc
    change U i j * (star U) l k = V i j * (star V) l k at hh
    calc
      U i j * M j l * (star U) l k = M j l * (U i j * (star U) l k) := by ring
      _ = M j l * (V i j * (star V) l k) := by rw [hh]
      _ = V i j * M j l * (star V) l k := by ring
  · intro h
    ext ⟨i, k⟩ ⟨j, l⟩
    have hh := congrArg (fun A : Operator ι => A i k) (h (matrixUnit j l))
    simpa [conjugationCoordinates, conjugation, matrixUnit, Matrix.mul_apply,
      ite_and, mul_ite, ite_mul] using hh

theorem unitary_conjugationCoordinates_eq_iff_projectivelyEquivalent [Nonempty ι]
    (U V : Operator ι) (hU : IsUnitary U) (hV : IsUnitary V) :
    conjugationCoordinates U = conjugationCoordinates V ↔ ProjectivelyEquivalent U V := by
  exact (conjugationCoordinates_eq_iff U V).trans
    (unitary_conjugation_eq_iff_projectivelyEquivalent U V hU hV)

/-- Finite coordinate images give finite images in the exact global-phase quotient. -/
theorem finite_projectiveImage_of_finite_conjugationCoordinates [Nonempty ι]
    (S : Set (Operator ι)) (hunit : ∀ U ∈ S, IsUnitary U)
    (hfinite : (conjugationCoordinates '' S).Finite) :
    (projectiveClass '' S).Finite := by
  classical
  let chooseClass : Operator (ι × ι) → ProjectiveOperator ι := fun A =>
    if h : ∃ U : Operator ι, U ∈ S ∧ conjugationCoordinates U = A then
      projectiveClass (Classical.choose h)
    else projectiveClass (1 : Operator ι)
  have hchoose (U : Operator ι) (hUS : U ∈ S) :
      chooseClass (conjugationCoordinates U) = projectiveClass U := by
    dsimp only [chooseClass]
    split_ifs with h
    · have hv := Classical.choose_spec h
      have hp : ProjectivelyEquivalent (Classical.choose h) U :=
        (unitary_conjugationCoordinates_eq_iff_projectivelyEquivalent
          (Classical.choose h) U (hunit _ hv.1) (hunit U hUS)).mp hv.2
      exact Quotient.sound hp
    · exact False.elim (h ⟨U, hUS, rfl⟩)
  refine (hfinite.image chooseClass).subset ?_
  rintro a ⟨U, hUS, rfl⟩
  exact ⟨conjugationCoordinates U, ⟨U, hUS, rfl⟩, hchoose U hUS⟩

end CriticalDepth
