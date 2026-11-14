import ShorNativeParentLayer

/-!
# Arity of the Shor cell transitions

All targets of a pivot come from its own sector and the assignment of
targets to pivot and offset is injective.
-/

namespace CriticalDepth.FaultShorSaturation

variable {n : ℕ}

theorem transitionParent_targetCount (q : ℕ) (A A' D D' : Finset (Fin n))
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (eA : (A' \ A : Finset (Fin n)) ≃ A × Fin (q - 1))
    (eD : (D \ D' : Finset (Fin n)) ≃ D' × Fin (q - 1))
    (a : Fin n) :
    (targetSites (transitionParent A A' D D' q eA eD) a).card ≤ q - 1 := by
  classical
  let p := transitionParent A A' D D' q eA eD
  let targets := targetSites p a
  have hp (i : targets) : p i.val = some a := (Finset.mem_filter.mp i.property).2
  let offset (i : targets) : Fin (q - 1) :=
    if hi : i.val ∈ A' \ A then (eA ⟨i.val, hi⟩).2
    else if hj : i.val ∈ D \ D' then (eD ⟨i.val, hj⟩).2
    else False.elim (by have h := hp i; simp [p, transitionParent, hi, hj] at h)
  have memA (i : targets) (hi : i.val ∈ A' \ A) :
      (eA ⟨i.val, hi⟩).1.val = a := by
    simpa [p, transitionParent, hi] using hp i
  have memD (i : targets) (hi : i.val ∉ A' \ A) (hj : i.val ∈ D \ D') :
      (eD ⟨i.val, hj⟩).1.val = a := by
    simpa [p, transitionParent, hi, hj] using hp i
  have exc (i : targets) (hi : i.val ∉ A' \ A) : i.val ∈ D \ D' := by
    by_contra hj
    have h := hp i
    simp [p, transitionParent, hi, hj] at h
  have hcross (i j : targets) (hi : i.val ∈ A' \ A) (hj : j.val ∉ A' \ A) : False := by
    have ha : a ∈ A := memA i hi ▸ (eA ⟨i.val, hi⟩).1.property
    have hd : a ∈ D' := memD j hj (exc j hj) ▸ (eD ⟨j.val, exc j hj⟩).1.property
    exact Finset.disjoint_left.mp hA'D (hAA' ha) (hD'D hd)
  have hinj : Function.Injective offset := by
    intro i j heq
    by_cases hi : i.val ∈ A' \ A <;> by_cases hj : j.val ∈ A' \ A
    · have hv := eA.injective (Prod.ext (Subtype.ext ((memA i hi).trans (memA j hj).symm))
        (by simpa only [offset, dite_eq_left hi, dite_eq_left hj] using heq))
      exact Subtype.ext (congrArg (fun z : (A' \ A : Finset (Fin n)) => z.val) hv)
    · exact (hcross i j hi hj).elim
    · exact (hcross j i hj hi).elim
    · have hi' := exc i hi
      have hj' := exc j hj
      have hv := eD.injective
        (Prod.ext (Subtype.ext ((memD i hi hi').trans (memD j hj hj').symm))
          (by simpa only [offset, dite_eq_right hi, dite_eq_right hj, dite_eq_left hi',
            dite_eq_left hj'] using heq))
      exact Subtype.ext (congrArg (fun z : (D \ D' : Finset (Fin n)) => z.val) hv)
  simpa [targets, p] using Fintype.card_le_of_injective offset hinj

theorem transitionParent_arity (q : ℕ) (hq : 1 ≤ q) (A A' D D' : Finset (Fin n))
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (eA : (A' \ A : Finset (Fin n)) ≃ A × Fin (q - 1))
    (eD : (D \ D' : Finset (Fin n)) ≃ D' × Fin (q - 1))
    (a : Fin n) :
    (parentSites (transitionParent A A' D D' q eA eD) a).card ≤ q := by
  have h := transitionParent_targetCount q A A' D D' hAA' hD'D hA'D eA eD a
  unfold parentSites
  exact (Finset.card_insert_le _ _).trans (by omega)

#print axioms transitionParent_targetCount
#print axioms transitionParent_arity

end CriticalDepth.FaultShorSaturation