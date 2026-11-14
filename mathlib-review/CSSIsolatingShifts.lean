import CSSMixedConstancy

/-!
# Kernel shifts that isolate a single interaction

One shift uses a single prescribed site and avoids all neighbors of the
other prescribed site. The other shift avoids the whole neighborhood
of the first support except at its own prescribed site.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sparseShift_support_subset (a : BinaryWord ι) (i : ι)
    (T : Finset ι) (hT : ∀ j ∈ T, a j = 0) :
    binaryWordSupport ((Pi.single i 1 : BinaryWord ι) + a) ⊆
      insert i (binaryWordSupport a) := by
  intro j hj
  by_cases hji : j = i
  · exact Finset.mem_insert.mpr (Or.inl hji)
  · apply Finset.mem_insert.mpr
    right
    rw [binaryWordSupport, Finset.mem_filter]
    have hb : ((Pi.single i 1 : BinaryWord ι) + a) j ≠ 0 :=
      (Finset.mem_filter.mp hj).2
    exact ⟨Finset.mem_univ _, by simpa [Pi.add_apply, Pi.single_eq_of_ne hji] using hb⟩

theorem exists_isolating_kernel_shifts {b : ℕ} (B : Matrix (Fin b) ι (ZMod 2))
    (hRows : Function.Injective (fun a : Fin b → ZMod 2 => a ᵥ* B))
    (T R : ℕ) (hT₁ : R + 2 ≤ T) (hT₂ : 1 + (b + 1) * (R + 1) ≤ T)
    (hDist : ∀ w : BinaryWord ι, w ≠ 0 → (∃ a : Fin b → ZMod 2, a ᵥ* B = w) →
      T < wordWeight w)
    (neighbors : ι → Finset ι) (hcard : ∀ i, (neighbors i).card ≤ R)
    (hsymm : ∀ i j, i ∈ neighbors j ↔ j ∈ neighbors i)
    (i j : ι) (hij : i ≠ j) :
    ∃ z z' : BinaryWord ι,
      B *ᵥ z = 0 ∧ B *ᵥ z' = 0 ∧
      i ∈ binaryWordSupport z ∧ j ∈ binaryWordSupport z' ∧
      Disjoint (binaryWordSupport z) (binaryWordSupport z') ∧
      ∀ x ∈ binaryWordSupport z, ∀ y ∈ binaryWordSupport z',
        y ∈ neighbors x → x = i ∧ y = j := by
  classical
  let avoid := insert i (insert j (neighbors j))
  have hav : avoid.card ≤ T :=
    (Finset.card_insert_le _ _).trans (by
      have h := Finset.card_insert_le j (neighbors j)
      have h' := hcard j
      omega)
  obtain ⟨a, ha, haW, haK, hai⟩ := exists_sparse_kernel_word B avoid hRows
    (fun w hw hs => hav.trans_lt (hDist w hw hs)) i (Finset.mem_insert_self _ _)
  let z : BinaryWord ι := Pi.single i 1 + a
  let I := binaryWordSupport z
  have hI : I.card ≤ b + 1 := by
    have hs := Finset.card_le_card (sparseShift_support_subset a i avoid ha)
    have hc := Finset.card_insert_le i (binaryWordSupport a)
    have haW' : (binaryWordSupport a).card ≤ b := by

      have hCard : (binaryWordSupport a).card = wordWeight a := by
        unfold wordWeight
        congr 1
        ext i
        simp [binaryWordSupport]
      exact hCard.trans_le haW
    change (binaryWordSupport (Pi.single i 1 + a)).card ≤ b + 1
    exact hs.trans (hc.trans (Nat.succ_le_succ haW'))
  have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change z i ≠ 0
    rw [show z i = 1 from hai]
    decide⟩
  have noFirst (x : ι) (hx : x ∈ I) (hxi : x ≠ i) : x ∉ insert j (neighbors j) := by
    intro hbad
    have hz := (Finset.mem_filter.mp hx).2
    have hxAvoid : x ∈ avoid := Finset.mem_insert_of_mem hbad
    apply hz
    simp [z, Pi.add_apply, Pi.single_eq_of_ne hxi, ha x hxAvoid]
  let avoid' := insert j (I.biUnion fun x => insert x (neighbors x))
  have hav' : avoid'.card ≤ T := by
    calc
      _ ≤ (I.biUnion fun x => insert x (neighbors x)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ x ∈ I, (insert x (neighbors x)).card) + 1 :=
        Nat.succ_le_succ Finset.card_biUnion_le
      _ ≤ (∑ _x ∈ I, (R + 1)) + 1 := by
        exact Nat.succ_le_succ (Finset.sum_le_sum fun x _ =>
          (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (hcard x)))
      _ ≤ T := by
        simp only [Finset.sum_const_nat]
        have := Nat.mul_le_mul_right (R + 1) hI
        omega
  obtain ⟨a', ha', _, haK', haj⟩ := exists_sparse_kernel_word B avoid' hRows
    (fun w hw hs => hav'.trans_lt (hDist w hw hs)) j (Finset.mem_insert_self _ _)
  let z' : BinaryWord ι := Pi.single j 1 + a'
  have hjI' : j ∈ binaryWordSupport z' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change z' j ≠ 0
    rw [show z' j = 1 from haj]
    decide⟩
  have noSecond (y : ι) (hy : y ∈ binaryWordSupport z') (hyj : y ≠ j) :
      y ∉ I.biUnion (fun x => insert x (neighbors x)) := by
    intro hbad
    have hz := (Finset.mem_filter.mp hy).2
    have hyAvoid : y ∈ avoid' := Finset.mem_insert_of_mem hbad
    apply hz
    simp [z', Pi.add_apply, Pi.single_eq_of_ne hyj, ha' y hyAvoid]
  refine ⟨z, z', haK, haK', hiI, hjI', ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hx'
    by_cases he : x = j
    · subst x
      exact (noFirst j hx hij.symm) (Finset.mem_insert_self _ _)
    · exact (noSecond x hx' he) (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_self _ _⟩)
  · intro x hx y hy hEdge
    have hyj : y = j := by
      by_contra hn
      exact (noSecond y hy hn) (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_of_mem hEdge⟩)
    subst y
    refine ⟨?_, rfl⟩
    by_contra hne
    exact (noFirst x hx hne) (Finset.mem_insert_of_mem ((hsymm x j).mpr hEdge))

#print axioms exists_isolating_kernel_shifts

end CriticalDepth.Manuscript20261114.CSSCheckSpaces