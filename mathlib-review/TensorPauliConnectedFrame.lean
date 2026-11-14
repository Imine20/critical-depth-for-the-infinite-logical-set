import TensorPauliConjugation
import Mathlib.Logic.Relation

/-!
# Pauli rotations from a connected logical frame

Quarter-turn conjugation propagates two-site Pauli rotations over an edge
path. All strings then follow by induction over their supports.
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open Relation

noncomputable section

variable {k : ℕ} (G : Subgroup (PU (QubitBasis k)))

/-- Pauli label equal to a and b at the indicated two distinct sites. -/
def pairPauli (i j : Fin k) (a b : SinglePauli) : Fin k → SinglePauli :=
  fun u => if u = i then a else if u = j then b else .I

private theorem exists_pauli_factor_pair {r : SinglePauli} (hr : r ≠ .I) :
    ∃ a b, pauliLabelsAnticommute a b ∧ unsignedPauliProduct a b = r := by
  cases r with
  | I => exact (hr rfl).elim
  | X => exact ⟨.Y, .Z, by decide, rfl⟩
  | Y => exact ⟨.Z, .X, by decide, rfl⟩
  | Z => exact ⟨.X, .Y, by decide, rfl⟩

private theorem replace_pauli_label_pair {a b : SinglePauli}
    (ha : a ≠ .I) (hb : b ≠ .I) (hab : a ≠ b) :
    pauliLabelsAnticommute (unsignedPauliProduct a b) a ∧
      unsignedPauliProduct (unsignedPauliProduct a b) a = b := by
  cases a <;> cases b <;> simp_all [unsignedPauliProduct, pauliLabelsAnticommute]

private theorem hasTensorPauliRotations_identity :
    HasTensorPauliRotations G (fun _ => .I) := by
  intro t
  have hOne : pauliMatrix (0 : Fin 4) (fun _ : Fin k => SinglePauli.I) = 1 := by
    rw [pauliMatrix_zero_eq_tensorEntries]
    exact tensorEntries_one
  have hEq : projectiveMk (QubitBasis k) (tensorPauliRotation (fun _ => .I) t) =
      projectiveMk (QubitBasis k) 1 := by
    apply (projectiveMk_eq_iff _ _ _).mpr
    refine ⟨(Circle.exp t : ℂ), circle_star_mul_self _, ?_⟩
    change rotation (pauliMatrix 0 (fun _ : Fin k => .I)) t = (Circle.exp t : ℂ) • 1
    rw [hOne, Circle.coe_exp, Complex.exp_ofReal_mul_I]
    simp [rotation, affine, add_smul, mul_comm]
  rw [hEq, map_one]
  exact G.one_mem

private theorem hasTensorPauliRotations_replace
    (site : ∀ i a, HasTensorPauliRotations G (singleSitePauli i a))
    {p : Fin k → SinglePauli} (hp : HasTensorPauliRotations G p)
    (i : Fin k) (hi : p i ≠ .I) (b : SinglePauli) (hb : b ≠ .I) :
    HasTensorPauliRotations G (Function.update p i b) := by
  by_cases h : p i = b
  · convert hp using 1
    funext j
    by_cases hj : j = i <;> simp [Function.update, hj, h]
  let a := unsignedPauliProduct (p i) b
  obtain ⟨ha, hab⟩ := replace_pauli_label_pair hi hb h
  have hs := hasTensorPauliRotations_unsignedProduct G (singleSitePauli i a) p i
    (site i a) hp (by simpa [singleSitePauli, a] using ha)
    (by intro j hj; simp [singleSitePauli, hj, pauliLabelsAnticommute])
  convert hs using 1
  funext j
  by_cases hj : j = i
  · subst j
    simpa [singleSitePauli, a] using hab.symm
  · simp [Function.update, hj, singleSitePauli, unsignedPauliProduct]

private theorem all_singleSite_from_XZ
    (hX : ∀ i, HasTensorPauliRotations G (singleSitePauli i .X))
    (hZ : ∀ i, HasTensorPauliRotations G (singleSitePauli i .Z)) :
    ∀ i a, HasTensorPauliRotations G (singleSitePauli i a) := by
  intro i a
  cases a with
  | I =>
    have he : singleSitePauli i .I = fun _ => .I := by funext j; simp [singleSitePauli]
    rw [he]
    exact hasTensorPauliRotations_identity G
  | X => exact hX i
  | Z => exact hZ i
  | Y =>
    have hs := hasTensorPauliRotations_unsignedProduct G
      (singleSitePauli i .X) (singleSitePauli i .Z) i (hX i) (hZ i)
      (by simp [singleSitePauli, pauliLabelsAnticommute])
      (by intro j hj; simp [singleSitePauli, hj, pauliLabelsAnticommute])
    convert hs using 1
    funext j
    by_cases hj : j = i <;> simp [singleSitePauli, hj, unsignedPauliProduct]

private theorem all_pair_from_ZZ
    (site : ∀ i a, HasTensorPauliRotations G (singleSitePauli i a))
    {i j : Fin k} (hij : i ≠ j) (hZZ : HasTensorPauliRotations G (pairPauli i j .Z .Z))
    {a b : SinglePauli} (ha : a ≠ .I) (hb : b ≠ .I) :
    HasTensorPauliRotations G (pairPauli i j a b) := by
  have h1 : HasTensorPauliRotations G (pairPauli i j a .Z) := by
    have hh := hasTensorPauliRotations_replace G site hZZ i (by simp [pairPauli]) a ha
    convert hh using 1
    funext u
    by_cases hu : u = i <;> simp [pairPauli, Function.update, hu]
  have hh := hasTensorPauliRotations_replace G site h1 j
    (by simp [pairPauli, Ne.symm hij]) b hb
  convert hh using 1
  funext u
  by_cases hu : u = j
  · subst u
    simp [pairPauli, Ne.symm hij]
  · simp [pairPauli, Function.update, hu]

private theorem pairZZ_compose
    (site : ∀ i a, HasTensorPauliRotations G (singleSitePauli i a))
    {i j l : Fin k} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (h₁ : HasTensorPauliRotations G (pairPauli i j .Z .Z))
    (h₂ : HasTensorPauliRotations G (pairPauli j l .Z .Z)) :
    HasTensorPauliRotations G (pairPauli i l .Z .Z) := by
  let p := pairPauli i j .Z .X
  let q := pairPauli j l .Y .Z
  let r := pairPauli i j .Y .Z
  let w : Fin k → SinglePauli := fun u => unsignedPauliProduct (p u) (q u)
  have hp : HasTensorPauliRotations G p :=
    all_pair_from_ZZ G site hij h₁ (by decide) (by decide)
  have hq : HasTensorPauliRotations G q :=
    all_pair_from_ZZ G site hjl h₂ (by decide) (by decide)
  have hr : HasTensorPauliRotations G r :=
    all_pair_from_ZZ G site hij h₁ (by decide) (by decide)
  have hw : HasTensorPauliRotations G w := by
    apply hasTensorPauliRotations_unsignedProduct G p q j hp hq
    · simp [p, q, pairPauli, Ne.symm hij, pauliLabelsAnticommute]
    · intro u hu
      by_cases hui : u = i
      · subst u; simp [p, q, pairPauli, hij, hil, pauliLabelsAnticommute]
      · simp [p, pairPauli, hui, hu, pauliLabelsAnticommute]
  have hProd := hasTensorPauliRotations_unsignedProduct G r w i hr hw
    (by simp [w, p, q, r, pairPauli, hij, hil, unsignedPauliProduct, pauliLabelsAnticommute])
    (by
      intro u hu
      by_cases huj : u = j
      · subst u
        simp [w, p, q, r, pairPauli, Ne.symm hij, unsignedPauliProduct, pauliLabelsAnticommute]
      · simp [r, pairPauli, hu, huj, pauliLabelsAnticommute])
  have hProd' : HasTensorPauliRotations G (pairPauli i l .X .Z) := by
    convert hProd using 1
    funext u
    by_cases hui : u = i
    · subst u; simp [r, w, p, q, pairPauli, hij, hil, unsignedPauliProduct]
    by_cases huj : u = j
    · subst u
      simp [r, w, p, q, pairPauli, Ne.symm hij, hjl, unsignedPauliProduct]
    · simp [r, w, p, q, pairPauli, hui, huj, unsignedPauliProduct]
  have hLast := hasTensorPauliRotations_replace G site hProd' i (by simp [pairPauli]) .Z (by decide)
  convert hLast using 1
  funext u
  by_cases hu : u = i <;> simp [Function.update, pairPauli, hu]

private theorem pairZZ_of_path
    (site : ∀ i a, HasTensorPauliRotations G (singleSitePauli i a))
    {E : Fin k → Fin k → Prop}
    (hedge : ∀ i j, E i j → i ≠ j → HasTensorPauliRotations G (pairPauli i j .Z .Z))
    {i j : Fin k} (hPath : ReflTransGen E i j) :
    i ≠ j → HasTensorPauliRotations G (pairPauli i j .Z .Z) := by
  induction hPath with
  | refl => intro h; exact (h rfl).elim
  | @tail j l _ hEdge ih =>
    intro hil
    by_cases hij : i = j
    · subst j; exact hedge _ _ hEdge hil
    by_cases hjl : j = l
    · subst l; exact ih hij
    exact pairZZ_compose G site hij hjl hil (ih hij) (hedge _ _ hEdge hjl)

private theorem all_strings_from_sites_pairs
    (site : ∀ i a, HasTensorPauliRotations G (singleSitePauli i a))
    (pair : ∀ i j, i ≠ j → ∀ a b, a ≠ .I → b ≠ .I →
      HasTensorPauliRotations G (pairPauli i j a b))
    (p : Fin k → SinglePauli) :
    HasTensorPauliRotations G p := by
  generalize he : (pauliSupport p).card = m
  induction m using Nat.strong_induction_on generalizing p with
  | h m ih =>
    by_cases hm : 1 < (pauliSupport p).card
    · obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp hm
      have hip : p i ≠ .I := (Finset.mem_filter.mp hi).2
      have hjp : p j ≠ .I := (Finset.mem_filter.mp hj).2
      obtain ⟨a, b, hab, hprod⟩ := exists_pauli_factor_pair hjp
      let q := pairPauli j i a (p i)
      let r : Fin k → SinglePauli := fun u => if u = i then .I else if u = j then b else p u
      have hSupp : pauliSupport r = (pauliSupport p).erase i := by
        ext u
        by_cases hui : u = i
        · subst u; simp [pauliSupport, r]
        by_cases huj : u = j
        · subst u
          simp [pauliSupport, r, Ne.symm hij, hab.2.1, hjp]
        · simp [pauliSupport, r, hui, huj]
      have hLt : (pauliSupport r).card < m := by
        rw [hSupp, ← he]
        exact Finset.card_erase_lt_of_mem hi
      have hq : HasTensorPauliRotations G q := pair j i hij.symm a (p i) hab.1 hip
      have hr := ih _ hLt r rfl
      have hs := hasTensorPauliRotations_unsignedProduct G q r j hq hr
        (by simpa [q, r, pairPauli, Ne.symm hij] using hab)
        (by
          intro u huj
          by_cases hui : u = i
          · subst u; simp [q, r, pauliLabelsAnticommute]
          · simp [q, pairPauli, hui, huj, pauliLabelsAnticommute])
      convert hs using 1
      funext u
      by_cases hui : u = i
      · subst u; cases h : p i <;> simp [q, r, pairPauli, hij, h, unsignedPauliProduct]
      by_cases huj : u = j
      · subst u; simpa [q, r, pairPauli, Ne.symm hij] using hprod.symm
      · simp [q, r, pairPauli, hui, huj, unsignedPauliProduct]
    · by_cases has : (pauliSupport p).Nonempty
      · obtain ⟨i, hi⟩ := has
        have hh : (pauliSupport p).card ≤ 1 := Nat.le_of_not_gt hm
        have heq : p = singleSitePauli i (p i) := by
          funext u
          by_cases hu : u = i
          · subst u; simp [singleSitePauli]
          · have hOff : p u = .I := by
              by_contra hn
              exact hu (Finset.card_le_one_iff.mp hh
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩) hi)
            simp [singleSitePauli, hu, hOff]
        rw [heq]
        exact site i (p i)
      · have heq : p = fun _ => .I := by
          funext u
          by_contra hu
          exact has ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
        rw [heq]
        exact hasTensorPauliRotations_identity G

/-- Single X and Z axes and ZZ on a connected set of edges suffice to
obtain all logical Pauli rotations by exact finite words. -/
theorem hasAllTensorPauliRotations_of_connectedFrame
    (E : Fin k → Fin k → Prop) (hConnected : ∀ i j, ReflTransGen E i j)
    (hX : ∀ i, HasTensorPauliRotations G (singleSitePauli i .X))
    (hZ : ∀ i, HasTensorPauliRotations G (singleSitePauli i .Z))
    (hZZ : ∀ i j, E i j → i ≠ j → HasTensorPauliRotations G (pairPauli i j .Z .Z)) :
    ∀ p, HasTensorPauliRotations G p := by
  have hSite := all_singleSite_from_XZ G hX hZ
  apply all_strings_from_sites_pairs G hSite
  intro i j hij a b ha hb
  exact all_pair_from_ZZ G hSite hij
    (pairZZ_of_path G hSite hZZ (hConnected i j) hij) ha hb

#print axioms hasAllTensorPauliRotations_of_connectedFrame

end

end CriticalDepth.Manuscript20261114
