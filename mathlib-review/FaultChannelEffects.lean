import FaultCPTPRepresentation
import FaultEntanglementFidelity

/-!
The effect formulation of trace distance for density matrices.
-/

namespace CriticalDepth.FaultChannelEffects

open Matrix CriticalDepth.FaultCPTPRepresentation
open scoped BigOperators ComplexOrder Kronecker

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsEffect (E : Matrix ι ι ℂ) : Prop :=
    E.PosSemidef ∧ (1 - E).PosSemidef

def IsDensity (D : Matrix ι ι ℂ) : Prop :=
    D.PosSemidef ∧ D.trace = 1

def effectValue (E A : Matrix ι ι ℂ) : ℝ := (E * A).trace.re

theorem real_sSup_le_of_nonneg {S : Set ℝ} {b : ℝ}
    (h : ∀ x ∈ S, x ≤ b) (hb : 0 ≤ b) : sSup S ≤ b := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Real.sSup_empty]
    exact hb
  · exact csSup_le hS h

theorem effectValue_add (E A B : Matrix ι ι ℂ) :
    effectValue E (A + B) = effectValue E A + effectValue E B := by
  simp only [effectValue, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem effectValue_sub (E A B : Matrix ι ι ℂ) :
    effectValue E (A - B) = effectValue E A - effectValue E B := by
  simp only [effectValue, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

theorem effectValue_smul (r : ℝ) (E A : Matrix ι ι ℂ) :
    effectValue E ((r : ℂ) • A) = r * effectValue E A := by
  simp only [effectValue, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem effectValue_self_of_trace_one {E A : Matrix ι ι ℂ} (hA : A.trace = 1) :
    effectValue (1 - E) A = 1 - effectValue E A := by
  simp only [effectValue, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hA,
    Complex.sub_re, Complex.one_re]

theorem posSemidef_factor_conjTranspose (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = B * B.conjTranspose := by
  let U : Matrix ι ι ℂ := hA.1.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (Real.sqrt (hA.1.eigenvalues i) : ℂ))
  let B := U * D
  have hDstar : D.conjTranspose = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
  have hDsq : D * D = Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
  refine ⟨B, ?_⟩
  calc
    A = U * Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * U.conjTranspose := by
      simpa only [U, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hA.1.spectral_theorem
    _ = B * B.conjTranspose := by
      rw [show B = U * D from rfl, Matrix.conjTranspose_mul, hDstar, ← hDsq]
      noncomm_ring

theorem effectValue_nonneg_of_posSemidef {E A : Matrix ι ι ℂ}
    (hE : E.PosSemidef) (hA : A.PosSemidef) : 0 ≤ effectValue E A := by
  obtain ⟨B, rfl⟩ := posSemidef_factor_conjTranspose A hA
  have ht : (E * (B * B.conjTranspose)).trace = (B.conjTranspose * E * B).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (E * B), Matrix.mul_assoc]
  rw [effectValue, ht]
  exact (Complex.nonneg_iff.mp (hE.conjTranspose_mul_mul_same B).trace_nonneg).1

theorem effectValue_mem_Icc {E A : Matrix ι ι ℂ} (hE : IsEffect E) (hA : IsDensity A) :
    effectValue E A ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨effectValue_nonneg_of_posSemidef hE.1 hA.1, ?_⟩
  have h := effectValue_nonneg_of_posSemidef hE.2 hA.1
  rw [effectValue_self_of_trace_one hA.2] at h
  linarith

theorem effectValue_difference_abs_le_one {E A B : Matrix ι ι ℂ}
    (hE : IsEffect E) (hA : IsDensity A) (hB : IsDensity B) :
    |effectValue E (A - B)| ≤ 1 := by
  rw [effectValue_sub, abs_le]
  have ha := effectValue_mem_Icc hE hA
  have hb := effectValue_mem_Icc hE hB
  exact ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩

theorem projector_isEffect (P : Matrix ι ι ℂ) (hHerm : P.IsHermitian) (hIdem : P * P = P) :
    IsEffect P := by
  refine ⟨?_, ?_⟩
  · have h := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [hHerm.eq, hIdem] at h
  · have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hHerm.eq] at h
    have he : (1 - P) * (1 - P) = 1 - P := by
      calc
        _ = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hIdem, sub_add_cancel]
    rwa [he] at h

#print axioms effectValue_mem_Icc
#print axioms projector_isEffect

end

end CriticalDepth.FaultChannelEffects