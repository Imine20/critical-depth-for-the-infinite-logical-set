import ExactGivensCompiler
import ExactSerialSynthesis
import SynthesisFiniteWords

/-!
# Compile the Givens word into a serial native circuit
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Relation

noncomputable section

variable {n k : ℕ} {C : Code n (fun _ => 2) (2 ^ k) 1} {ι : Type*} [Fintype ι]

private theorem PauliRotationFamily.expand_mapped_list
    (F : PauliRotationFamily C ι) (P : Matrix.unitaryGroup (QubitBasis k) ℂ →* PU (Fin (2 ^ k)))
    (L : List (Matrix.unitaryGroup (QubitBasis k) ℂ))
    (hL : ∀ U ∈ L, P U ∈ Subgroup.closure F.alphabet) :
    ∃ W : List (PU (Fin (2 ^ k))),
      (∀ V ∈ W, V ∈ F.alphabet) ∧ W.prod = P L.prod := by
  induction L with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons U L ih =>
    obtain ⟨W, hW, he⟩ := F.exists_word_of_mem_closure (hL U (List.mem_cons_self ..))
    obtain ⟨R, hR, hr⟩ := ih (fun V hV => hL V (List.mem_cons_of_mem U hV))
    refine ⟨W ++ R, ?_, ?_⟩
    · intro V hV
      rcases List.mem_append.mp hV with hV | hV
      · exact hW V hV
      · exact hR V hV
    · rw [List.prod_append, he, hr, List.prod_cons, map_mul]

/-- The exact Givens factors, each expanded into a finite word in the
connected frame, give a complete native logical circuit. Its depth is at
most the number of frame primitives times the common compression budget. -/
theorem PauliRotationFamily.exists_native_serial_givens_of_connected_axes
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
    (W : PU (Fin (2 ^ k))) :
    ∃ (A : Matrix.unitaryGroup (QubitBasis k) ℂ) (L : TensorPauliWord k)
      (R : List (PU (Fin (2 ^ k)))),
      P (projectiveMk (QubitBasis k) A) = W ∧
      IsTensorPauliWord L ∧ L.prod = A ∧
      (∀ V ∈ R, V ∈ F.alphabet) ∧ R.prod = W ∧
      W ∈ nativeLogicalImage C.encoding q
        (R.length * Arithmetic.criticalDepth q F.maxWeight) := by
  let G := (Subgroup.closure F.alphabet).comap P.toMonoidHom
  have hAll : ∀ w, HasTensorPauliRotations G w :=
    hasAllTensorPauliRotations_of_connectedFrame G E hConnected hX hZ hZZ
  obtain ⟨V, hV⟩ := P.surjective W
  obtain ⟨A, hA⟩ : ∃ A : Matrix.unitaryGroup (QubitBasis k) ℂ,
      projectiveMk (QubitBasis k) A = V := QuotientGroup.mk_surjective V
  obtain ⟨L, hL, hp⟩ := unitary_exists_tensorPauliWord_of_givens e A
  let Q := P.toMonoidHom.comp (projectiveMk (QubitBasis k))
  have hFactor (B : Matrix.unitaryGroup (QubitBasis k) ℂ) (hB : B ∈ L) :
      Q B ∈ Subgroup.closure F.alphabet := by
    obtain ⟨w, t, rfl⟩ := hL B hB
    exact hAll w t
  obtain ⟨R, hR, he⟩ := F.expand_mapped_list Q L hFactor
  have hOut : P (projectiveMk (QubitBasis k) A) = W := (congrArg P hA).trans hV
  have hProd : R.prod = W := he.trans ((congrArg Q hp).trans hOut)
  refine ⟨A, L, R, hOut, hL, hp, hR, hProd, ?_⟩
  rw [← hProd]
  apply nativeLogicalImage_list_prod
  intro U hU
  exact F.alphabet_subset_nativeLogicalImage hn q hq hWeight (hR U hU)

#print axioms PauliRotationFamily.exists_native_serial_givens_of_connected_axes

end

end CriticalDepth.Manuscript20261114
