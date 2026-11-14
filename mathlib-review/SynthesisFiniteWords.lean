import SupplementSynthesis

/-!
# Finite words in the physical Pauli rotation alphabet
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2

noncomputable section

variable {n K : ℕ} {ι : Type*} {C : Code n (fun _ => 2) K 1}

/-- Negative angles give the inverses of all prescribed generators. -/
theorem PauliRotationFamily.alphabet_inv_mem (F : PauliRotationFamily C ι)
    {W : PU (Fin K)} (hW : W ∈ F.alphabet) : W⁻¹ ∈ F.alphabet := by
  obtain ⟨i, t, rfl⟩ := hW
  refine ⟨i, -t, ?_⟩
  unfold projectiveRotation
  rw [← map_inv]
  apply congrArg (projectiveMk (Fin K))
  apply Subtype.ext
  exact (star_rotation (F.selfAdjoint i) t).symm

/-- Membership in the generated subgroup is a finite word of actual
registered rotations. The order is the ordinary matrix product order. -/
theorem PauliRotationFamily.exists_word_of_mem_closure (F : PauliRotationFamily C ι)
    {W : PU (Fin K)} (hW : W ∈ Subgroup.closure F.alphabet) :
    ∃ L : List (PU (Fin K)), (∀ U ∈ L, U ∈ F.alphabet) ∧ L.prod = W := by
  induction hW using Subgroup.closure_induction with
  | mem W hW => exact ⟨[W], by simpa using hW, by simp⟩
  | one => exact ⟨[], by simp, rfl⟩
  | mul U V hU hV ihU ihV =>
    obtain ⟨L, hL, rfl⟩ := ihU
    obtain ⟨R, hR, rfl⟩ := ihV
    refine ⟨L ++ R, ?_, List.prod_append⟩
    intro W hW
    rcases List.mem_append.mp hW with h | h
    · exact hL W h
    · exact hR W h
  | inv W hW ih =>
    obtain ⟨L, hL, rfl⟩ := ih
    refine ⟨(L.map fun U => U⁻¹).reverse, ?_, (List.prod_inv_reverse L).symm⟩
    intro U hU
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hU)
    exact F.alphabet_inv_mem (hL V hV)

/-- A universally generating frame gives a finite word of individually
bounded-depth native logical gates for every exact projective target. -/
theorem PauliRotationFamily.exists_native_word [Fintype ι] (F : PauliRotationFamily C ι)
    (hn : 0 < n) (q : ℕ) (hq : 2 ≤ q) (hD : 2 ≤ F.maxWeight)
    (hTop : Subgroup.closure F.alphabet = ⊤) (W : PU (Fin K)) :
    ∃ L : List (PU (Fin K)),
      (∀ U ∈ L, U ∈ nativeLogicalImage C.encoding q (Arithmetic.criticalDepth q F.maxWeight)) ∧
      L.prod = W := by
  have hW : W ∈ Subgroup.closure F.alphabet := hTop ▸ Subgroup.mem_top W
  obtain ⟨L, hL, hProd⟩ := F.exists_word_of_mem_closure hW
  exact ⟨L, fun U hU => F.alphabet_subset_nativeLogicalImage hn q hq hD (hL U hU), hProd⟩

#print axioms PauliRotationFamily.exists_word_of_mem_closure
#print axioms PauliRotationFamily.exists_native_word

end

end CriticalDepth.Manuscript20261114
