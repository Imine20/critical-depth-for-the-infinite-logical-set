import ExactGivensNativeWord
import NativeScalarPhase

/-!
# Exact Givens compilation of a chosen logical unitary
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Relation
open scoped Kronecker

noncomputable section

variable {n k : ℕ} {C : Code n (fun _ => 2) (2 ^ k) 1} {ι : Type*} [Fintype ι]

/-- Starting from a logical unitary rather than its projective class,
the exact compiler produces a finite Pauli word and an actual native
circuit on the original encoding. The frame word includes one zero-angle rotation, so the scalar correction fits inside the depth bound. -/
theorem PauliRotationFamily.exists_native_exact_givens_of_connected_axes
    (F : PauliRotationFamily C ι) (e : QubitBasis k ≃ Fin (2 ^ k))
    (P : PU (QubitBasis k) ≃* PU (Fin (2 ^ k)))
    (hn : 0 < n) (q : ℕ) (hq : 2 ≤ q) (hWeight : 2 ≤ F.maxWeight)
    (E : Fin k → Fin k → Prop) (hConnected : ∀ i j, ReflTransGen E i j)
    (hX : ∀ i t,
      P (projectiveMk (QubitBasis k) (tensorPauliRotation (singleSitePauli i .X) t)) ∈
        Subgroup.closure F.alphabet)
    (hZ : ∀ i t,
      P (projectiveMk (QubitBasis k) (tensorPauliRotation (singleSitePauli i .Z) t)) ∈
        Subgroup.closure F.alphabet)
    (hZZ : ∀ i j, E i j → i ≠ j → ∀ t,
      P (projectiveMk (QubitBasis k) (tensorPauliRotation (pairPauli i j .Z .Z) t)) ∈
        Subgroup.closure F.alphabet)
    (A : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ) :
    ∃ (B : Matrix.unitaryGroup (QubitBasis k) ℂ) (L : TensorPauliWord k)
      (R : List (PU (Fin (2 ^ k)))),
      P (projectiveMk (QubitBasis k) B) = projectiveMk (Fin (2 ^ k)) A ∧
      IsTensorPauliWord L ∧ L.prod = B ∧
      (∀ V ∈ R, V ∈ F.alphabet) ∧ R.prod = projectiveMk (Fin (2 ^ k)) A ∧
      ∃ s ≤ R.length * Arithmetic.criticalDepth q F.maxWeight,
        ∃ c : NativeCircuit n (fun _ => 2) s, NativeCircuitAllowed q c ∧
          (nativeCircuitEval c).val * C.encoding =
            C.encoding * (A.val ⊗ₖ (1 : Operator (Fin 1))) := by
  obtain ⟨B, L, R, hA, hL, hb, hR, hprod, _⟩ :=
    F.exists_native_serial_givens_of_connected_axes e P hn q hq hWeight E hConnected
      hX hZ hZZ (projectiveMk (Fin (2 ^ k)) A)
  classical
  have hIndex : Nonempty ι := by
    by_contra h
    letI : IsEmpty ι := not_nonempty_iff.mp h
    have he : F.maxWeight = 0 := by simp [PauliRotationFamily.maxWeight]
    omega
  let i := Classical.choice hIndex
  have hOne : (1 : PU (Fin (2 ^ k))) ∈ F.alphabet := by
    refine ⟨i, 0, ?_⟩
    unfold projectiveRotation
    rw [← map_one (projectiveMk (Fin (2 ^ k)))]
    apply congrArg (projectiveMk (Fin (2 ^ k)))
    apply Subtype.ext
    exact rotation_zero _
  let W := (1 : PU (Fin (2 ^ k))) :: R
  have hWord : ∀ U ∈ W, U ∈ F.alphabet := by
    intro U hU
    rcases List.mem_cons.mp hU with rfl | hU
    · exact hOne
    · exact hR U hU
  have hProd : W.prod = projectiveMk (Fin (2 ^ k)) A := by simpa [W] using hprod
  let d := Arithmetic.criticalDepth q F.maxWeight
  have hSize : 1 ≤ W.length * d := by
    have hd : 1 ≤ d := one_le_criticalDepth_of_two_le q F.maxWeight hq hWeight
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by simp [W]) (by omega))
  have hImage : projectiveMk (Fin (2 ^ k)) A ∈ nativeLogicalImage C.encoding q (W.length * d) := by
    rw [← hProd]
    apply nativeLogicalImage_list_prod
    intro U hU
    exact F.alphabet_subset_nativeLogicalImage hn q hq hWeight (hWord U hU)
  obtain ⟨s, hs, c, hc, he⟩ := nativeLogicalImage_exact_lift C.encoding A hImage
  exact ⟨B, L, W, hA, hL, hb, hWord, hProd, s, by simpa only [max_eq_right hSize] using hs, c, hc, he⟩

#print axioms PauliRotationFamily.exists_native_exact_givens_of_connected_axes

end

end CriticalDepth.Manuscript20261114
