import ExactControlProjector
import TensorPauliTangents
import ExactConditionalPhase

/-!
# Controlled X and Z rotation generators
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped BigOperators

noncomputable section

variable {k : ℕ}

/-- Multiply a control Z mask by a Pauli on a distinct target. -/
def controlledPauliWord (T : Finset (Fin k)) (j : Fin k) (A : SinglePauli) :
    Fin k → SinglePauli := fun i => if i = j then A else zSubset T i

theorem zSubset_mul_targetPauli (T : Finset (Fin k)) (j : Fin k) (hj : j ∉ T) (A : SinglePauli) :
    pauliMatrix 0 (zSubset T) * pauliMatrix 0 (singleSitePauli j A) =
      pauliMatrix 0 (controlledPauliWord T j A) := by
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  congr 1
  funext i
  by_cases hi : i = j
  · subst i
    simp [zSubset, hj, controlledPauliWord, singleSitePauli, SinglePauli.matrix]
  · simp [hi, controlledPauliWord, singleSitePauli, SinglePauli.matrix]

/-- In a control subspace, the target operator has the finite commuting
Pauli expansion used in the exact compiler. -/
theorem controlProjector_mul_targetPauli_eq_sum
    (B : Finset (Fin k)) (y : QubitBasis k) (j : Fin k) (hj : j ∉ B) (A : SinglePauli) :
    controlProjector B y * pauliMatrix 0 (singleSitePauli j A) =
      (2 : ℂ)⁻¹ ^ B.card •
        ∑ T ∈ B.powerset, (∏ i ∈ T, logicalBitSign (y i)) •
          pauliMatrix 0 (controlledPauliWord T j A) := by
  rw [controlProjector_eq_pauliSum, smul_mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  rw [smul_mul_assoc, zSubset_mul_targetPauli T j
    (fun h => hj ((Finset.mem_powerset.mp hT) h)) A]

/-- Terms in the expansion commute. Each target letter coincides,
and all positions away from the target carry Z or identity. -/
theorem controlledPauliWord_commute (T S : Finset (Fin k))
    (j : Fin k) (A : SinglePauli) :
    Commute (pauliMatrix 0 (controlledPauliWord T j A))
      (pauliMatrix 0 (controlledPauliWord S j A)) := by
  show _ * _ = _ * _
  rw [unphased_pauliMatrix_commutation]
  have hs : (∏ i, (controlledPauliWord T j A i).commutationSign
    (controlledPauliWord S j A i)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = j
    · subst i
      simp [controlledPauliWord, SinglePauli.commutationSign]
    · by_cases hT : i ∈ T <;> by_cases hS : i ∈ S <;>
        simp [controlledPauliWord, zSubset, SinglePauli.commutationSign, hi, hT, hS]
  rw [hs, one_smul]

section
open scoped Matrix.Norms.L2Operator

/-- The controlled rotation is the exponential of the projector times
the target axis, with the same angle on the selected two-level block. -/
def conditionalRotation (B : Finset (Fin k)) (y : QubitBasis k)
    (j : Fin k) (A : SinglePauli) (t : ℝ) : Operator (QubitBasis k) :=
  NormedSpace.exp (((Complex.I * (t : ℂ)) • controlProjector B y) *
    pauliMatrix 0 (singleSitePauli j A))

theorem conditionalRotation_eq_finite_tensorPauliWord
    (B : Finset (Fin k)) (y : QubitBasis k) (j : Fin k) (hj : j ∉ B)
    (A : SinglePauli) (t : ℝ) :
    ∃ L : List (Matrix.unitaryGroup (QubitBasis k) ℂ),
      (∀ U ∈ L, ∃ T : Finset (Fin k), T ⊆ B ∧
        U = tensorPauliRotation (controlledPauliWord T j A) (conditionalPauliAngle B T y t)) ∧
      L.prod.val = conditionalRotation B y j A t := by
  classical
  let f : Finset (Fin k) → Fin k → SinglePauli := fun T =>
    if j ∈ T then zSubset T else controlledPauliWord T j A
  let rot := fun T : Finset (Fin k) => tensorPauliRotation (f T) (conditionalPauliAngle B T y t)
  let M := fun T : Finset (Fin k) =>
    (Complex.I * (conditionalPauliAngle B T y t : ℂ)) • pauliMatrix 0 (f T)
  have hf {T : Finset (Fin k)} (hT : T ∈ B.powerset) : f T = controlledPauliWord T j A := by
    have hn : j ∉ T := fun h => hj ((Finset.mem_powerset.mp hT) h)
    simp [f, hn]
  have hexp : conditionalRotation B y j A t = NormedSpace.exp (∑ T ∈ B.powerset, M T) := by
    unfold conditionalRotation
    rw [smul_mul_assoc, controlProjector_mul_targetPauli_eq_sum B y j hj A, smul_smul,
      Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro T hT
    unfold M
    rw [hf hT, smul_smul]
    congr 1
    change _ * (∏ i ∈ T, logicalBitSign (y i)) = _
    rw [show (∏ i ∈ T, logicalBitSign (y i)) =
        (((∏ i ∈ T, if y i = 0 then (1 : ℝ) else -1) : ℝ) : ℂ) by
      push_cast
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : y i = 0 <;> simp [logicalBitSign, hi]]
    unfold conditionalPauliAngle
    push_cast
    ring
  have hcomm (T S : Finset (Fin k)) (hT : T ∈ B.powerset) (hS : S ∈ B.powerset) :
      Commute (M T) (M S) := by
    unfold M
    rw [hf hT, hf hS]
    exact ((controlledPauliWord_commute T S j A).smul_left _).smul_right _
  have hprod (L : List (Finset (Fin k))) (hL : ∀ T ∈ L, T ∈ B.powerset) :
      (L.map rot).prod.val = NormedSpace.exp (L.map M).sum := by
    induction L with
    | nil => simp
    | cons a L ih =>
      have ha := hL a (List.mem_cons_self ..)
      have htail : ∀ T ∈ L, T ∈ B.powerset :=
        fun T hT => hL T (List.mem_cons_of_mem a hT)
      have hc : Commute (M a) (L.map M).sum := by
        apply Commute.list_sum_right
        intro b hb
        obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hb
        exact hcomm a T ha (htail T hT)
      change (rot a).val * (L.map rot).prod.val = NormedSpace.exp (M a + (L.map M).sum)
      rw [Matrix.exp_add_of_commute _ _ hc]
      rw [ih htail]
      congr 1
      exact rotation_eq_exp_involution (unphased_pauliMatrix_sq _) _
  refine ⟨B.powerset.toList.map rot, ?_, ?_⟩
  · intro U h
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp h
    have hmem := Finset.mem_toList.mp hT
    exact ⟨T, Finset.mem_powerset.mp hmem, by simp [rot, hf hmem]⟩
  · rw [hexp, hprod _ (fun T hT => Finset.mem_toList.mp hT)]
    have hs := Finset.sum_map_toList B.powerset M
    exact congrArg (fun A : Operator (QubitBasis k) => NormedSpace.exp A) hs

#print axioms conditionalRotation_eq_finite_tensorPauliWord

end

#print axioms zSubset_mul_targetPauli
#print axioms controlProjector_mul_targetPauli_eq_sum
#print axioms controlledPauliWord_commute

end

end CriticalDepth.Manuscript20261114
