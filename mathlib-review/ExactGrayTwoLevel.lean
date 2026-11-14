import ExactControlledWord
import ExactGrayRouting
import ExactGivensStep
import BinaryPermutationUnitary

/-!
# Exact Gray compilation of a two-level unitary
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open CriticalDepth.BinaryPermutationUnitary

noncomputable section

variable {k : ℕ}

private theorem basisPermutation_mul_right_apply (p : Equiv.Perm (QubitBasis k))
    (A : Operator (QubitBasis k)) (x y : QubitBasis k) :
    (A * basisPermutation p) x y = A x (p y) := by
  classical
  simp only [Matrix.mul_apply, basisPermutation_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

private theorem twoLevel_on_pair (e : RowPair (QubitBasis k)) (A : Operator (Fin 2))
    (a b : Fin 2) : twoLevel e A (e a) (e b) = A a b := by
  unfold twoLevel
  change fromBlocks A _ _ _ ((rowPairSplit e).symm (e a)) ((rowPairSplit e).symm (e b)) = _
  have he (t : Fin 2) : (rowPairSplit e).symm (e t) = Sum.inl t :=
    (rowPairSplit e).symm_apply_apply (Sum.inl t)
  rw [he a, he b]
  rfl

private theorem twoLevel_one_on_complement (e : RowPair (QubitBasis k)) (A : Operator (Fin 2))
    (x y : QubitBasis k) (hx : x ∉ Set.range e) (hy : y ∉ Set.range e) :
    twoLevel e A x y = if x = y then 1 else 0 := by
  have h (z : QubitBasis k) (hz : z ∉ Set.range e) :
      (rowPairSplit e).symm z = Sum.inr ⟨z, hz⟩ := by
    apply (rowPairSplit e).injective
    exact (rowPairSplit e).apply_symm_apply z
  unfold twoLevel
  change fromBlocks A _ _ _ ((rowPairSplit e).symm x) ((rowPairSplit e).symm y) = _
  rw [h x hx, h y hy]
  simp [Matrix.fromBlocks, Matrix.one_apply, Subtype.ext_iff]

private theorem twoLevel_zero_mixed (e : RowPair (QubitBasis k)) (A : Operator (Fin 2))
    (a : Fin 2) (y : QubitBasis k) (hy : y ∉ Set.range e) :
    twoLevel e A (e a) y = 0 ∧ twoLevel e A y (e a) = 0 := by
  have h₁ : (rowPairSplit e).symm (e a) = Sum.inl a :=
    (rowPairSplit e).symm_apply_apply (Sum.inl a)
  have h₂ : (rowPairSplit e).symm y = Sum.inr ⟨y, hy⟩ := by
    apply (rowPairSplit e).injective
    exact (rowPairSplit e).apply_symm_apply y
  constructor
  · change fromBlocks A _ _ _ ((rowPairSplit e).symm (e a)) ((rowPairSplit e).symm y) = _
    rw [h₁, h₂]
    rfl
  · change fromBlocks A _ _ _ ((rowPairSplit e).symm y) ((rowPairSplit e).symm (e a)) = _
    rw [h₁, h₂]
    rfl

private theorem twoLevel_eq_controlled_after_routing (e : RowPair (QubitBasis k))
    (A : Operator (Fin 2)) (p : Equiv.Perm (QubitBasis k))
    (hGray : GrayAdjacent (p (e 0)) (p (e 1))) :
    ∃ (j : Fin k) (Q : Operator (Fin 2)), IsUnitary A → IsUnitary Q ∧
      basisPermutation p * twoLevel e A * basisPermutation p.symm =
        controlledTarget j (p (e 0)) Q := by
  classical
  obtain ⟨j, hj, hRest⟩ := hGray
  let b := (p (e 0)) j
  let t : Equiv.Perm (Fin 2) := if b = 0 then Equiv.refl _ else Equiv.swap 0 1
  have ht₀ : t 0 = (p (e 0)) j := by
    unfold t
    by_cases hb : b = 0
    · rw [ite_eq_left hb, Equiv.refl_apply]
      exact hb.symm
    · have h01 (a : Fin 2) : a = 0 ∨ a = 1 := by decide +revert
      have h : b = 1 := (h01 b).resolve_left hb
      rw [ite_eq_right hb, Equiv.swap_apply_left]
      exact h.symm
  have ht₁ : t 1 = (p (e 1)) j := by
    have hne : t 1 ≠ (p (e 0)) j := by
      rw [← ht₀]
      exact fun h => (by decide : (1 : Fin 2) ≠ 0) (t.injective h)
    have h01 (a : Fin 2) : a = 0 ∨ a = 1 := by decide +revert
    rcases h01 (t 1) with h | h <;> rcases h01 ((p (e 1)) j) with h' | h' <;>
      rcases h01 ((p (e 0)) j) with h0 | h0 <;> simp_all
  let Q := reindexAlgEquiv ℂ ℂ t A
  refine ⟨j, Q, fun hA => ⟨?_, ?_⟩⟩
  · have hStar : reindexAlgEquiv ℂ ℂ t (star A) = star Q := rfl
    constructor
    · rw [← hStar, ← map_mul, hA.1, map_one]
    · rw [← hStar, ← map_mul, hA.2, map_one]
  · ext x y
    rw [basisPermutation_mul_right_apply, basisPermutation_mul_apply, controlledTarget_apply]
    have hbij (a : Fin 2) : (p (e a)) j = t a := by
      fin_cases a
      · exact ht₀.symm
      · exact ht₁.symm
    have hmem (w : QubitBasis k) : p.symm w ∈ Set.range e ↔
        controlBits j w = controlBits j (p (e 0)) := by
      constructor
      · rintro ⟨a, ha⟩
        have hw : w = p (e a) := (p.apply_symm_apply w).symm.trans (congrArg p ha.symm)
        rw [hw]
        fin_cases a
        · rfl
        · funext i
          exact (hRest i.val i.property).symm
      · intro hw
        let a := t.symm (w j)
        refine ⟨a, p.injective ?_⟩
        rw [p.apply_symm_apply]
        funext i
        by_cases hi : i = j
        · subst i; rw [hbij, Equiv.apply_symm_apply]
        · have h := congrFun hw ⟨i, hi⟩
          have hFixed (u : Fin 2) : p (e u) i = p (e 0) i := by
            fin_cases u
            · rfl
            · exact (hRest i hi).symm
          exact (hFixed a).trans h.symm
    by_cases hx : p.symm x ∈ Set.range e <;> by_cases hy : p.symm y ∈ Set.range e
    · obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      have hxc := (hmem x).mp ⟨a, ha⟩
      have hyc := (hmem y).mp ⟨b, hb⟩
      rw [← ha, ← hb, twoLevel_on_pair, ite_eq_left (hxc.trans hyc.symm), ite_eq_left hxc]
      have ex : x = p (e a) := (p.apply_symm_apply x).symm.trans (congrArg p ha.symm)
      have ey : y = p (e b) := (p.apply_symm_apply y).symm.trans (congrArg p hb.symm)
      change A a b = A (t.symm (x j)) (t.symm (y j))
      rw [ex, ey, hbij, hbij, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    · obtain ⟨a, ha⟩ := hx
      have hxc := (hmem x).mp ⟨a, ha⟩
      rw [← ha, (twoLevel_zero_mixed e A a (p.symm y) hy).1]
      exact (ite_eq_right (fun h => hy ((hmem y).mpr (h.symm.trans hxc)))).symm
    · obtain ⟨b, hb⟩ := hy
      have hyc := (hmem y).mp ⟨b, hb⟩
      rw [← hb, (twoLevel_zero_mixed e A b (p.symm x) hx).2]
      exact (ite_eq_right (fun h => hx ((hmem x).mpr (h.trans hyc)))).symm
    · rw [twoLevel_one_on_complement e A _ _ hx hy]
      have hxc : controlBits j x ≠ controlBits j (p (e 0)) :=
        fun h => hx ((hmem x).mpr h)
      by_cases hxy : controlBits j x = controlBits j y
      · have he : x = y ↔ x j = y j := by
          refine ⟨fun h => congrArg (fun x : QubitBasis k => x j) h, ?_⟩
          intro h
          exact (splitTargetBit j).symm.injective (Prod.ext h hxy)
        have hyc : controlBits j y ≠ controlBits j (p (e 0)) := fun h => hxc (hxy.trans h)
        simp [p.symm.injective.eq_iff, hxy, hxc, hyc, he, Matrix.one_apply]
      · have he : x ≠ y := fun h => hxy (congrArg (controlBits j) h)
        simp [p.symm.injective.eq_iff, hxy, he]

/-- Gray routing conjugates any two-level unitary to a fully controlled
one-qubit block. The implementing basis permutation is explicitly the
product of the prescribed adjacent swaps. -/
theorem twoLevel_exists_gray_controlled
    (e : RowPair (QubitBasis k)) (A : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (L : List (QubitBasis k × QubitBasis k)) (j : Fin k) (Q : Matrix.unitaryGroup (Fin 2) ℂ),
      (∀ a ∈ L, GrayAdjacent a.1 a.2) ∧
      basisPermutation (graySwapPermutation L) * twoLevel e A.val *
        basisPermutation (graySwapPermutation L).symm =
          controlledTarget j (e 0) Q.val := by
  have hne : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (e.injective h)
  obtain ⟨z, L, hAdj, hL, hFix, hMove⟩ := gray_routing_swaps hne
  let p := graySwapPermutation L
  have h0 : p (e 0) = e 0 := (graySwapPermutation_apply L _).trans hFix
  have h1 : p (e 1) = z := (graySwapPermutation_apply L _).trans hMove
  have hGray : GrayAdjacent (p (e 0)) (p (e 1)) := by rwa [h0, h1]
  obtain ⟨j, Q, h⟩ := twoLevel_eq_controlled_after_routing e A.val p hGray
  obtain ⟨hQ, hEq⟩ := h A.property
  refine ⟨L, j, ⟨Q, hQ⟩, hL, ?_⟩
  rw [← h0]
  exact hEq

#print axioms twoLevel_exists_gray_controlled

end

end CriticalDepth.Manuscript20261114
