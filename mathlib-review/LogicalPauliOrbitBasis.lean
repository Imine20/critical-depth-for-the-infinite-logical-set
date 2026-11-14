import LogicalPauliOrbit
import CSSCodePauliChecks
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Unitary realization of a logical Pauli frame
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.FaultShorSaturation Matrix

noncomputable section

variable {k : ℕ}
local notation "α" => Fin (2 ^ k)

private def setOfOnes (b : QubitBasis k) : Finset (Fin k) :=
  Finset.univ.filter fun i => b i ≠ 0

private theorem setOfOnes_injective : Function.Injective (setOfOnes (k := k)) := by
  intro x y h
  funext i
  have he := Finset.ext_iff.mp h i
  simp only [setOfOnes, Finset.mem_filter, Finset.mem_univ, true_and] at he
  have h01 (b : Fin 2) : b = 0 ∨ b = 1 := by decide +revert
  rcases h01 (x i) with hx | hx <;> rcases h01 (y i) with hy | hy <;> simp_all

private theorem normalized_vacuum (F : LogicalPauliFrame (Fin k) α) :
    ∃ v : α → ℂ, star v ⬝ᵥ v = 1 ∧ ∀ i, F.Z i *ᵥ v = v := by
  obtain ⟨w, hw, hZ⟩ := F.exists_vacuum
  let a := ∑ j : α, ‖w j‖ ^ 2
  have hReal : star w ⬝ᵥ w = (a : ℂ) := by
    have hterm (z : ℂ) : star z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm]
      exact Complex.mul_conj' z
    unfold a dotProduct
    push_cast
    exact Finset.sum_congr rfl (fun j _ => hterm (w j))
  have hNonneg : 0 ≤ a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hNe : a ≠ 0 := by
    intro ha
    apply hw
    have hAll := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset α)) =>
      sq_nonneg ‖w j‖)).mp ha
    funext j
    exact norm_eq_zero.mp (by nlinarith [hAll j (Finset.mem_univ j)])
  let c := Real.sqrt a
  have hc : c ^ 2 = a := Real.sq_sqrt hNonneg
  have hcNZ : (c : ℂ) ≠ 0 := by
    have h : c ≠ 0 := by intro he; rw [he, zero_pow (by decide)] at hc; exact hNe hc.symm
    exact_mod_cast h
  refine ⟨(c : ℂ)⁻¹ • w, ?_, fun i => by rw [Matrix.mulVec_smul, hZ]⟩
  have hcStar : star (c : ℂ) = c := Complex.conj_ofReal c
  rw [star_smul, star_inv₀, hcStar, smul_dotProduct, dotProduct_smul, hReal]
  have hC : (c : ℂ) ^ 2 = (a : ℂ) := by exact_mod_cast hc
  rw [← hC]
  simp only [smul_eq_mul]
  field_simp

private def orbitBasis (F : LogicalPauliFrame (Fin k) α) (v : α → ℂ)
    (b : QubitBasis k) : α → ℂ := F.xProduct (setOfOnes b) *ᵥ v

private theorem orbitBasis_X (F : LogicalPauliFrame (Fin k) α) (v : α → ℂ)
    (i : Fin k) (b : QubitBasis k) :
    F.X i *ᵥ orbitBasis F v b = orbitBasis F v (Function.update b i (if b i = 0 then 1 else 0)) := by
  unfold orbitBasis
  rw [Matrix.mulVec_mulVec, F.x_mul_xProduct_toggle]
  have he : (if i ∈ setOfOnes b then (setOfOnes b).erase i else insert i (setOfOnes b)) =
      setOfOnes (Function.update b i (if b i = 0 then 1 else 0)) := by
    by_cases h : b i = 0
    · have hi : i ∉ setOfOnes b := by simp [setOfOnes, h]
      rw [ite_eq_right hi, ite_eq_left h]
      ext j
      by_cases hj : j = i
      · subst j; simp [setOfOnes, h]
      · simp [setOfOnes, hj, Function.update_of_ne hj]
    · have hi : i ∈ setOfOnes b := by simp [setOfOnes, h]
      rw [ite_eq_left hi, ite_eq_right h]
      ext j
      by_cases hj : j = i
      · subst j; simp [setOfOnes, h]
      · simp [setOfOnes, hj, Function.update_of_ne hj]
  rw [he]

private theorem orbitBasis_Z (F : LogicalPauliFrame (Fin k) α) (v : α → ℂ)
    (hv : ∀ i, F.Z i *ᵥ v = v) (i : Fin k) (b : QubitBasis k) :
    F.Z i *ᵥ orbitBasis F v b = (if b i = 0 then (1 : ℂ) else -1) • orbitBasis F v b := by
  unfold orbitBasis
  rw [F.z_mulVec_xProduct _ _ _ hv]
  by_cases h : b i = 0 <;> simp [setOfOnes, h]

private theorem singleSite_Z_apply (i : Fin k) (x y : QubitBasis k) :
    pauliMatrix 0 (singleSitePauli i .Z) x y =
      if x = y then (if y i = 0 then (1 : ℂ) else -1) else 0 := by
  have hWord : singleSitePauli i .Z = cssZWord (Pi.single i (1 : CSSBit)) := by
    funext j
    by_cases h : j = i
    · subst j; simp [singleSitePauli, cssZWord]
    · simp [singleSitePauli, cssZWord, h]
  rw [hWord]
  let M := pauliMatrix 0 (cssZWord (Pi.single i (1 : CSSBit)))
  change M.col y x = _
  rw [← Matrix.mulVec_single_one M y]
  change (pauliMatrix 0 (cssZWord (Pi.single i (1 : CSSBit))) *ᵥ
    (Pi.single y (1 : ℂ))) x = _
  rw [cssZWord_mulVec, dotProduct_single_one]
  by_cases h : x = y
  · subst y
    have hBit (b : Fin 2) : cssSign (qubitBitEquiv b) =
        (if b = 0 then (1 : ℂ) else -1) := by
      fin_cases b <;> simp [cssSign, qubitBitEquiv]
    simpa [Pi.single_eq_same, binaryWordEquiv] using hBit (x i)
  · simp [Pi.single_eq_of_ne h, h]

private theorem singleSite_X_apply (i : Fin k) (x y : QubitBasis k) :
    pauliMatrix 0 (singleSitePauli i .X) x y =
      if x = Function.update y i (if y i = 0 then 1 else 0) then 1 else 0 := by
  rw [pauliMatrix_zero_eq_tensorEntries]
  change (∏ j, (singleSitePauli i .X j).matrix (x j) (y j)) = _
  by_cases h : x = Function.update y i (if y i = 0 then 1 else 0)
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro j _
    by_cases hj : j = i
    · subst j
      have he := congrFun h i
      have hw (a b : Fin 2) (hb : a = if b = 0 then 1 else 0) :
          SinglePauli.X.matrix a b = 1 := by
        fin_cases a <;> fin_cases b <;> simp_all [SinglePauli.matrix]
      exact (by simpa [singleSitePauli] using hw (x i) (y i) (by simpa using he))
    · have he : x j = y j := by simpa [Function.update_of_ne hj] using congrFun h j
      simp [singleSitePauli, SinglePauli.matrix, hj, Matrix.one_apply, he]
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    by_cases hj' : j = i
    · subst j
      have hw (a b : Fin 2) (hb : a ≠ if b = 0 then 1 else 0) :
          SinglePauli.X.matrix a b = 0 := by
        fin_cases a <;> fin_cases b <;> simp_all [SinglePauli.matrix]
      exact (by simpa [singleSitePauli] using hw (x i) (y i) (by simpa using hj))
    · have he : x j ≠ y j := by simpa [Function.update_of_ne hj'] using hj
      simp [singleSitePauli, SinglePauli.matrix, hj', Matrix.one_apply, he]

/-- The logical X and Z matrices of a frame are the conventional tensor
Paulis in one common orthonormal basis. -/
theorem LogicalPauliFrame.exists_unitary_tensor_basis
    (F : LogicalPauliFrame (Fin k) α) (e : QubitBasis k ≃ α) :
    ∃ U : Matrix.unitaryGroup α ℂ,
      (∀ i, F.X i = Unitary.conjStarAlgAut ℂ (Operator α) U
        (Matrix.reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (singleSitePauli i .X)))) ∧
      (∀ i, F.Z i = Unitary.conjStarAlgAut ℂ (Operator α) U
        (Matrix.reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (singleSitePauli i .Z)))) := by
  classical
  obtain ⟨v, hv, hZ⟩ := normalized_vacuum F
  let A : Operator α := fun u j => orbitBasis F v (e.symm j) u
  have hA : A.conjTranspose * A = 1 := by
    ext a b
    change star (orbitBasis F v (e.symm a)) ⬝ᵥ orbitBasis F v (e.symm b) = (1 : Operator α) a b
    by_cases hab : a = b
    · subst b
      rw [Matrix.one_apply_eq, orbitBasis, F.xProduct_orthogonal_norm, hv]
    · rw [Matrix.one_apply_ne hab]
      exact F.xProduct_orthogonal_distinct _ _
        (fun he => hab (e.symm.injective (setOfOnes_injective he))) v hZ
  have hU : IsUnitary A := ⟨hA, mul_eq_one_comm.mp hA⟩
  let U : Matrix.unitaryGroup α ℂ := ⟨A, hU⟩
  have finish (M B : Operator α) (h : M * A = A * B) :
      M = Unitary.conjStarAlgAut ℂ (Operator α) U B := by
    change M = A * B * A.conjTranspose
    rw [← h, Matrix.mul_assoc, show A * A.conjTranspose = 1 from hU.2, Matrix.mul_one]
  refine ⟨U, ?_, ?_⟩
  · intro i
    apply finish
    ext u j
    change (F.X i *ᵥ orbitBasis F v (e.symm j)) u =
      ∑ a, A u a * pauliMatrix 0 (singleSitePauli i .X) (e.symm a) (e.symm j)
    rw [orbitBasis_X]
    let b := Function.update (e.symm j) i (if (e.symm j) i = 0 then 1 else 0)
    simp only [singleSite_X_apply]
    have he (a : α) : e.symm a = b ↔ a = e b := by
      constructor
      · intro h
        exact (e.apply_symm_apply a).symm.trans (congrArg e h)
      · rintro rfl; exact e.symm_apply_apply b
    simp_rw [show Function.update (e.symm j) i (if (e.symm j) i = 0 then 1 else 0) = b from rfl,
      he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, A, e.symm_apply_apply]
  · intro i
    apply finish
    ext u j
    change (F.Z i *ᵥ orbitBasis F v (e.symm j)) u =
      ∑ a, A u a * pauliMatrix 0 (singleSitePauli i .Z) (e.symm a) (e.symm j)
    rw [orbitBasis_Z _ _ hZ]
    simp only [singleSite_Z_apply, e.symm.injective.eq_iff, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp [A, mul_comm]
    · intro a _ ha
      simp [ha]
    · simp

#print axioms LogicalPauliFrame.exists_unitary_tensor_basis

end

end CriticalDepth.Manuscript20261114
