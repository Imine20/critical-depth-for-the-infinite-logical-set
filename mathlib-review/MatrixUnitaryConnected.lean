import UnitaryCurveProducts
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Finite matrix unitary groups are path connected

A finite matrix spectrum allows an argument function on the whole spectrum.
Its continuous functional calculus is a self-adjoint logarithm.
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.ReviewV2
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matrix_expUnitary_arg (u : Matrix.unitaryGroup ι ℂ) :
    selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u := by
  apply Subtype.ext
  let A := (u : Matrix ι ι ℂ)
  let f : ℂ → ℂ := fun z => Complex.arg z
  letI : IsStarNormal A := isStarNormal_of_mem_unitary u.property
  have hf : ContinuousOn f (spectrum ℂ A) := A.finite_spectrum.continuousOn f
  have hg : ContinuousOn (fun z : ℂ => NormedSpace.exp (Complex.I • z))
      (f '' spectrum ℂ A) := by
    rw [← Complex.exp_eq_exp_ℂ]
    exact (Complex.continuous_exp.comp (continuous_const_smul Complex.I)).continuousOn
  change (selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) : Matrix ι ι ℂ) = A
  rw [selfAdjoint.expUnitary_coe, Unitary.argSelfAdjoint_coe,
    ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul ..,
    ← cfc_comp' (hg := hg) (hf := hf)]
  conv_rhs => rw [← cfc_id' ℂ A]
  apply cfc_congr
  intro z hz
  have hn : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary u.property hz
  have he := Complex.norm_mul_exp_arg_mul_I z
  simpa [f, ← Complex.exp_eq_exp_ℂ, smul_eq_mul, mul_comm, hn] using he

/-- Every finite-dimensional complex matrix unitary admits a path to the
identity in the matrix-group topology. -/
theorem matrixUnitary_joined_one (u : Matrix.unitaryGroup ι ℂ) : Joined 1 u := by
  rw [← matrix_expUnitary_arg u]
  exact selfAdjoint.joined_one_expUnitary _

theorem matrixUnitary_pathConnectedSpace :
    PathConnectedSpace (Matrix.unitaryGroup ι ℂ) where
  nonempty := ⟨1⟩
  joined x y := (matrixUnitary_joined_one x).symm.trans (matrixUnitary_joined_one y)

/-- An open subgroup of the logical projective unitary group is all of it. -/
theorem projectiveUnitary_eq_top_of_open (G : Subgroup (PU ι))
    (hG : IsOpen (G : Set (PU ι))) : G = ⊤ := by
  letI : PathConnectedSpace (Matrix.unitaryGroup ι ℂ) := matrixUnitary_pathConnectedSpace
  let H := G.comap (projectiveMk ι)
  have ho : IsOpen (H : Set (Matrix.unitaryGroup ι ℂ)) :=
    hG.preimage (continuous_projectiveMk (ι := ι))
  have hc : IsClopen (H : Set (Matrix.unitaryGroup ι ℂ)) := ⟨H.isClosed_of_isOpen ho, ho⟩
  have hU : (H : Set (Matrix.unitaryGroup ι ℂ)) = Set.univ :=
    hc.eq_univ ⟨1, H.one_mem⟩
  apply top_unique
  intro x _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  change u ∈ H
  rw [← SetLike.mem_coe, hU]
  exact Set.mem_univ u

#print axioms matrixUnitary_joined_one
#print axioms projectiveUnitary_eq_top_of_open

end

end CriticalDepth.Manuscript20261114
