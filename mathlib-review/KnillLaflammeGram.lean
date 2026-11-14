import OrthogonalRecovery
import RecoveryCrossTerms
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Scalar cross terms and one finite Kraus recovery

This direction of Knill–Laflamme applies to arbitrary finite matrix error
branches. A scalar Gram matrix is obtained from any logical basis column
and hence is positive semidefinite. Its unitary diagonalization reduces
to the orthogonal Kraus construction. The following equivalence records
the resulting scalar action of the recovered operators and the finite
Kraus completeness constraint. The bridge to optimization over all CPTP
channels is a separate result.
-/

namespace CriticalDepth.KnillLaflammeGram

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

variable {Phys Log Hist : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log]
variable [Fintype Hist] [DecidableEq Hist]

private def mix (A : Hist → Matrix Phys Log ℂ) (V : Matrix Hist Hist ℂ)
    (j : Hist) : Matrix Phys Log ℂ := ∑ i, V i j • A i

private theorem gram_posSemidef (A : Hist → Matrix Phys Log ℂ)
    (G : Matrix Hist Hist ℂ) (a : Log)
    (hG : ∀ i j, (A i).conjTranspose * A j = G i j • (1 : Matrix Log Log ℂ)) :
    G.PosSemidef := by
  let T : Matrix Phys Hist ℂ := fun x j => A j x a
  have hEq : T.conjTranspose * T = G := by
    ext i j
    have h := congrFun (congrFun (hG i j) a) a
    change (∑ x, star (A i x a) * A j x a) = G i j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  rw [← hEq]
  exact Matrix.posSemidef_conjTranspose_mul_self T

private theorem mixed_crossTerm (A : Hist → Matrix Phys Log ℂ) (V G : Matrix Hist Hist ℂ)
    (hG : ∀ i j, (A i).conjTranspose * A j = G i j • (1 : Matrix Log Log ℂ))
    (a b : Hist) :
    (mix A V a).conjTranspose * mix A V b =
      (V.conjTranspose * G * V) a b • (1 : Matrix Log Log ℂ) := by
  classical
  simp only [mix, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, hG, Finset.smul_sum, smul_smul]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

private theorem mix_mul (A : Hist → Matrix Phys Log ℂ) (V W : Matrix Hist Hist ℂ)
    (j : Hist) : mix (mix A V) W j = mix A (V * W) j := by
  classical
  simp only [mix, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

private theorem mix_one (A : Hist → Matrix Phys Log ℂ) (j : Hist) :
    mix A 1 j = A j := by
  classical
  rw [mix, Finset.sum_eq_single j]
  · simp
  · intro i _ hne
    simp [Matrix.one_apply, hne]
  · simp

private theorem smul_identity_mul_adjoint (A B : Matrix Phys Log ℂ) (a b : ℂ) :
    (a • A).conjTranspose * (b • B) = (star a * b) • (A.conjTranspose * B) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- If every encoded error cross term is scalar, one trace-preserving
finite Kraus family has scalar action on every branch. No stabilizer or
orthogonality premise is imposed on the original branches. -/
theorem existsRecoveryKraus_of_scalarCrossTerms [Nonempty Log]
    (A : Hist → Matrix Phys Log ℂ) (G : Matrix Hist Hist ℂ)
    (hG : ∀ i j, (A i).conjTranspose * A j = G i j • (1 : Matrix Log Log ℂ)) :
    ∃ r : ℕ, ∃ (R : Fin r → Matrix Log Phys ℂ) (z : Fin r → Hist → ℂ),
      (∑ k, (R k).conjTranspose * R k) = 1 ∧
      ∀ k i, R k * A i = z k i • (1 : Matrix Log Log ℂ) := by
  classical
  let a : Log := Classical.choice inferInstance
  have hPSD := gram_posSemidef A G a hG
  let V := hPSD.1.eigenvectorUnitary
  let d := hPSD.1.eigenvalues
  have hd (j : Hist) : 0 ≤ d j := hPSD.eigenvalues_nonneg j
  have hDiag : (V : Matrix Hist Hist ℂ).conjTranspose * G * (V : Matrix Hist Hist ℂ) =
      Matrix.diagonal (fun j => (d j : ℂ)) := by
    simpa only [V, d, Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using
      hPSD.1.conjStarAlgAut_star_eigenvectorUnitary
  let B := mix A (V : Matrix Hist Hist ℂ)
  have hB (i j : Hist) : (B i).conjTranspose * B j =
      (Matrix.diagonal (fun k => (d k : ℂ))) i j • (1 : Matrix Log Log ℂ) := by
    rw [← hDiag]
    exact mixed_crossTerm A _ G hG i j
  have hBZero (j : Hist) (hj : ¬ 0 < d j) : B j = 0 := by
    have hzero : d j = 0 := le_antisymm (le_of_not_gt hj) (hd j)
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [Matrix.diagonal_apply_eq, hzero, Complex.ofReal_zero, zero_smul] using hB j j
  let Pos := {j : Hist // 0 < d j}
  let scale : Hist → ℂ := fun j => (Real.sqrt (d j) : ℝ)
  have hscale (j : Pos) : scale j ≠ 0 := by
    change ((Real.sqrt (d j) : ℝ) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.2 j.property).ne'
  have hscaleSq (j : Hist) : scale j * scale j = (d j : ℂ) := by
    change ((Real.sqrt (d j) : ℝ) : ℂ) * ((Real.sqrt (d j) : ℝ) : ℂ) = (d j : ℂ)
    exact_mod_cast Real.mul_self_sqrt (hd j)
  have hscaleStar (j : Hist) : star (scale j) = scale j := by simp [scale, Complex.conj_ofReal]
  let C : Pos → Matrix Phys Log ℂ := fun j => (scale j)⁻¹ • B j
  have hCiso (j : Pos) : (C j).conjTranspose * C j = 1 := by
    change ((scale j)⁻¹ • B j).conjTranspose * ((scale j)⁻¹ • B j) = 1
    rw [smul_identity_mul_adjoint, hB, Matrix.diagonal_apply_eq, smul_smul,
      star_inv₀, hscaleStar, ← hscaleSq]
    have hcoeff : ((scale j)⁻¹ * (scale j)⁻¹) * (scale j * scale j) = 1 := by
      field_simp [hscale j]
    rw [hcoeff, one_smul]
  have hCorth (i j : Pos) (hij : i ≠ j) : (C i).conjTranspose * C j = 0 := by
    have hne : (i : Hist) ≠ (j : Hist) := fun e => hij (Subtype.ext e)
    change ((scale i)⁻¹ • B i).conjTranspose * ((scale j)⁻¹ • B j) = 0
    rw [smul_identity_mul_adjoint, hB, Matrix.diagonal_apply_ne _ hne, zero_smul, smul_zero]
  let state : Log → ℂ := Pi.single a 1
  have hstate : (∑ l, star (state l) * state l) = 1 := by
    simp [state, Pi.single_apply]
  obtain ⟨R, hTP, z, hz⟩ := OrthogonalRecovery.existsRecoveryKraus_scalar C state
    hCiso hCorth hstate
  have hcomposeB (k : Pos ⊕ Phys) (j : Hist) : ∃ w : ℂ,
      R k * B j = w • (1 : Matrix Log Log ℂ) := by
    by_cases hpos : 0 < d j
    · let j' : Pos := ⟨j, hpos⟩
      have heq : B j = scale j • C j' := by
        change B j = scale j • ((scale j)⁻¹ • B j)
        rw [smul_smul, mul_inv_cancel₀ (hscale j'), one_smul]
      refine ⟨scale j * z k j', ?_⟩
      rw [heq, Matrix.mul_smul, hz, smul_smul]
    · exact ⟨0, by rw [hBZero j hpos, Matrix.mul_zero, zero_smul]⟩
  choose w hw using hcomposeB
  have hUnmix (j : Hist) : A j = mix B ((V : Matrix Hist Hist ℂ).conjTranspose) j := by
    symm
    rw [show B = mix A (V : Matrix Hist Hist ℂ) by rfl, mix_mul]
    change mix A ((V : Matrix Hist Hist ℂ) * star V) j = A j
    rw [Unitary.coe_mul_star_self, mix_one]
  have hcompose (k : Pos ⊕ Phys) (j : Hist) :
      R k * A j = (∑ i, ((V : Matrix Hist Hist ℂ).conjTranspose i j) * w k i) •
        (1 : Matrix Log Log ℂ) := by
    rw [hUnmix j]
    simp only [mix, Matrix.mul_sum, Matrix.mul_smul, hw, smul_smul, Finset.sum_smul]
  let e : (Pos ⊕ Phys) ≃ Fin (Fintype.card (Pos ⊕ Phys)) := Fintype.equivFin _
  refine ⟨_, R ∘ e.symm, (fun k j => ∑ i, ((V : Matrix Hist Hist ℂ).conjTranspose i j) *
    w (e.symm k) i), ?_, fun k j => hcompose (e.symm k) j⟩
  change (∑ k, (R (e.symm k)).conjTranspose * R (e.symm k)) = 1
  calc
    _ = ∑ k : Pos ⊕ Phys, (R k).conjTranspose * R k :=
      e.symm.sum_comp (fun k => (R k).conjTranspose * R k)
    _ = 1 := hTP

/-- Existence of a trace-preserving scalar-action finite Kraus recovery is
equivalent to scalar encoded error cross terms, for arbitrary finite branches. -/
theorem scalarCrossTerms_iff_recoveryKraus [Nonempty Log]
    (A : Hist → Matrix Phys Log ℂ) :
    (∃ G : Matrix Hist Hist ℂ, ∀ i j, (A i).conjTranspose * A j =
      G i j • (1 : Matrix Log Log ℂ)) ↔
    ∃ r : ℕ, ∃ (R : Fin r → Matrix Log Phys ℂ) (z : Fin r → Hist → ℂ),
      (∑ k, (R k).conjTranspose * R k) = 1 ∧
      ∀ k i, R k * A i = z k i • (1 : Matrix Log Log ℂ) := by
  constructor
  · rintro ⟨G, hG⟩
    exact existsRecoveryKraus_of_scalarCrossTerms A G hG
  · rintro ⟨r, R, z, hTP, hz⟩
    exact ⟨(fun i j => ∑ k, star (z k i) * z k j), fun i j =>
      CriticalDepth.Manuscript20261114.crossTerm_scalar_of_recoveryKraus (A i) (A j)
        R (fun k => z k i) (fun k => z k j) hTP (fun k => hz k i) (fun k => hz k j)⟩

#print axioms existsRecoveryKraus_of_scalarCrossTerms
#print axioms scalarCrossTerms_iff_recoveryKraus

end
end CriticalDepth.KnillLaflammeGram
