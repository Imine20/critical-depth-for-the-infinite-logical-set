import ExactGrayTwoLevel

/-!
# Finite tensor Pauli words for Gray transpositions and two-level blocks
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open CriticalDepth.BinaryPermutationUnitary

noncomputable section

variable {k : ℕ}

def permutationUnitary (p : Equiv.Perm (QubitBasis k)) :
    Matrix.unitaryGroup (QubitBasis k) ℂ :=
  ⟨basisPermutation p, basisPermutation_isUnitary p⟩

private theorem permutationUnitary_product (p q : Equiv.Perm (QubitBasis k)) :
    permutationUnitary q * permutationUnitary p = permutationUnitary (p.trans q) := by
  apply Subtype.ext
  exact basisPermutation_mul q p

private theorem permutationUnitary_inverse (p : Equiv.Perm (QubitBasis k)) :
    (permutationUnitary p)⁻¹ = permutationUnitary p.symm := by
  apply Subtype.ext
  exact basisPermutation_conjTranspose p

private theorem controlledTarget_X_eq_neighbor_swap (x y : QubitBasis k)
    (hxy : GrayAdjacent x y) :
    ∃ j : Fin k, controlledTarget j x SinglePauli.X.matrix = basisPermutation (Equiv.swap x y) := by
  classical
  obtain ⟨j, hj, hOther⟩ := hxy
  have hCon : controlBits j x = controlBits j y := by
    funext i
    exact hOther i.val i.property
  have hNe : x ≠ y := fun h => hj (congrArg (fun x : QubitBasis k => x j) h)
  let flip (z : QubitBasis k) := Function.update z j (if z j = 0 then 1 else 0)
  have hFlip : flip x = y := by
    funext i
    by_cases hi : i = j
    · subst i
      have h01 (b : Fin 2) : b = 0 ∨ b = 1 := by decide +revert
      rcases h01 (x j) with hx | hx <;> rcases h01 (y j) with hy | hy <;> simp_all [flip]
    · simpa [flip, Function.update_of_ne hi] using hOther i hi
  have hFlip' : flip y = x := by
    funext i
    by_cases hi : i = j
    · subst i
      have h01 (b : Fin 2) : b = 0 ∨ b = 1 := by decide +revert
      rcases h01 (x j) with hx | hx <;> rcases h01 (y j) with hy | hy <;> simp_all [flip]
    · simpa [flip, Function.update_of_ne hi] using (hOther i hi).symm
  have hControls (z : QubitBasis k) : controlBits j z = controlBits j x → z = x ∨ z = y := by
    intro hz
    by_cases hx : z j = x j
    · exact Or.inl ((splitTargetBit j).symm.injective (Prod.ext hx hz))
    · have h01 (b : Fin 2) : b = 0 ∨ b = 1 := by decide +revert
      have he : z j = y j := by
        rcases h01 (z j) with h | h <;> rcases h01 (x j) with hx' | hx' <;>
          rcases h01 (y j) with hy | hy <;> simp_all
      exact Or.inr ((splitTargetBit j).symm.injective (Prod.ext he (hz.trans hCon)))
  refine ⟨j, ?_⟩
  ext a z
  rw [controlledTarget_X_entry, basisPermutation_apply]
  by_cases hx : z = x
  · subst z
    rw [ite_eq_left rfl, Equiv.swap_apply_left]
    change (if a = flip x then 1 else 0) = _
    rw [hFlip]
  · by_cases hy : z = y
    · subst z
      rw [ite_eq_left hCon.symm, Equiv.swap_apply_right]
      change (if a = flip y then 1 else 0) = _
      rw [hFlip']
    · have hOff : controlBits j z ≠ controlBits j x := by
        intro h
        exact (hControls z h).elim hx hy
      rw [ite_eq_right hOff, Equiv.swap_apply_of_ne_of_ne hx hy]

private theorem neighbor_swap_mem_pauliWords
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis k) ℂ))
    (hS : ∀ w t, tensorPauliRotation w t ∈ S)
    (x y : QubitBasis k) (hxy : GrayAdjacent x y) :
    permutationUnitary (Equiv.swap x y) ∈ S := by
  obtain ⟨j, hj⟩ := controlledTarget_X_eq_neighbor_swap x y hxy
  let X : Matrix.unitaryGroup (Fin 2) ℂ := ⟨SinglePauli.X.matrix, singlePauli_isUnitary .X⟩
  obtain ⟨L, hL, hp⟩ := controlledTarget_exists_tensorPauliWord j x X
  have he : L.prod = permutationUnitary (Equiv.swap x y) := by
    apply Subtype.ext
    exact hp.trans hj
  rw [← he]
  apply S.list_prod_mem
  intro U hU
  obtain ⟨w, t, rfl⟩ := hL U hU
  exact hS w t

private theorem grayPermutation_mem_pauliWords
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis k) ℂ))
    (hS : ∀ w t, tensorPauliRotation w t ∈ S)
    (L : List (QubitBasis k × QubitBasis k))
    (hL : ∀ a ∈ L, GrayAdjacent a.1 a.2) :
    permutationUnitary (graySwapPermutation L) ∈ S := by
  induction L with
  | nil =>
    have he : permutationUnitary (graySwapPermutation ([] : List (QubitBasis k × QubitBasis k))) = 1 := by
      apply Subtype.ext
      ext a b
      change basisPermutation (Equiv.refl (QubitBasis k)) a b = (1 : Operator (QubitBasis k)) a b
      rw [basisPermutation_apply, Equiv.refl_apply, Matrix.one_apply]
    rw [he]
    exact S.one_mem
  | cons e L ih =>
    change permutationUnitary ((Equiv.swap e.1 e.2).trans (graySwapPermutation L)) ∈ S
    rw [← permutationUnitary_product]
    exact S.mul_mem (ih (fun a ha => hL a (List.mem_cons_of_mem e ha)))
      (neighbor_swap_mem_pauliWords S hS e.1 e.2 (hL e (List.mem_cons_self ..)))

private theorem twoLevel_mem_pauliWords
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis k) ℂ))
    (hS : ∀ w t, tensorPauliRotation w t ∈ S)
    (e : RowPair (QubitBasis k)) (A : Matrix.unitaryGroup (Fin 2) ℂ) :
    (⟨twoLevel e A.val, twoLevel_isUnitary e A.val A.property⟩ :
      Matrix.unitaryGroup (QubitBasis k) ℂ) ∈ S := by
  obtain ⟨L, j, B, hL, hEq⟩ := twoLevel_exists_gray_controlled e A
  let Aup := (⟨twoLevel e A.val, twoLevel_isUnitary e A.val A.property⟩ :
    Matrix.unitaryGroup (QubitBasis k) ℂ)
  let P := permutationUnitary (graySwapPermutation L)
  have hP : P ∈ S := grayPermutation_mem_pauliWords S hS L hL
  obtain ⟨M, hM, hMProd⟩ := controlledTarget_exists_tensorPauliWord j (e 0) B
  have hD : P * Aup * P⁻¹ = M.prod := by
    apply Subtype.ext
    rw [permutationUnitary_inverse]
    exact hEq.trans hMProd.symm
  have hMem : P * Aup * P⁻¹ ∈ S := by
    rw [hD]
    apply S.list_prod_mem
    intro U hU
    obtain ⟨w, t, rfl⟩ := hM U hU
    exact hS w t
  have hBack := S.mul_mem (S.mul_mem (S.inv_mem hP) hMem) hP
  simpa [mul_assoc] using hBack

def tensorPauliWordSubgroup (k : ℕ) : Subgroup (Matrix.unitaryGroup (QubitBasis k) ℂ) where
  carrier := {U | ∃ L : TensorPauliWord k, IsTensorPauliWord L ∧ L.prod = U}
  one_mem' := ⟨[], by simp [IsTensorPauliWord], rfl⟩
  mul_mem' := by
    rintro U V ⟨L, hL, rfl⟩ ⟨R, hR, rfl⟩
    refine ⟨L ++ R, ?_, List.prod_append⟩
    intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact hL W hW
    · exact hR W hW
  inv_mem' := by
    rintro U ⟨L, hL, rfl⟩
    refine ⟨(L.map fun W => W⁻¹).reverse, ?_, (List.prod_inv_reverse L).symm⟩
    intro W hW
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hW)
    obtain ⟨q, t, rfl⟩ := hL V hV
    refine ⟨q, -t, ?_⟩
    apply Subtype.ext
    exact star_rotation (unphased_pauliMatrix_selfAdjoint q) t

/-- An arbitrary two-level factor is an actual unitary product of tensor
Pauli rotations, using the selected Gray swaps, a conditional unitary and
the inverse swaps. -/
theorem twoLevel_exists_tensorPauliWord (e : RowPair (QubitBasis k))
    (A : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ L : TensorPauliWord k, IsTensorPauliWord L ∧ L.prod.val = twoLevel e A.val := by
  let S := tensorPauliWordSubgroup k
  have hS (w : Fin k → SinglePauli) (t : ℝ) : tensorPauliRotation w t ∈ S := by
    refine ⟨[tensorPauliRotation w t], ?_, by simp⟩
    intro U hU
    exact ⟨w, t, List.mem_singleton.mp hU⟩
  obtain ⟨L, hL, hprod⟩ := twoLevel_mem_pauliWords S hS e A
  exact ⟨L, hL, congrArg Subtype.val hprod⟩

#print axioms twoLevel_exists_tensorPauliWord

end

end CriticalDepth.Manuscript20261114
