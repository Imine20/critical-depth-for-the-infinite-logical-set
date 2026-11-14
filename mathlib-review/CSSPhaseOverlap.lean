import CSSPhaseDifferences

/-!
# CSS phase signs from overlapping kernel words

Two allowed words whose supports meet in one coordinate determine the
square of that coordinate's phase factor. Sparse kernel completion
provides such a pair under the check-space distance bound.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [CommGroup G]

/-- The product of the individual phase factors for the active bits. -/
def coordinatePhase (r : ι → G) (z : BinaryWord ι) : G :=
  ∏ j ∈ binaryWordSupport z, r j

private theorem binary_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have hv := a.val_lt
    have hz : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
    exact (ZMod.val_eq_one (by decide) a).mp (by omega)

private theorem coord_mem_support {z : BinaryWord ι} {j : ι} :
    j ∈ binaryWordSupport z ↔ z j ≠ 0 := by
  simp [binaryWordSupport]

private theorem coordinatePhase_eq_prod (r : ι → G) (z : BinaryWord ι) :
    coordinatePhase r z = ∏ j, if z j ≠ 0 then r j else 1 := by
  unfold coordinatePhase binaryWordSupport
  exact Finset.prod_filter _ _

/-- Products over two binary words multiply as their binary sum, with a
squared factor for each site in the intersection of their supports. -/
theorem coordinatePhase_mul_of_single_intersection (r : ι → G) (z z' : BinaryWord ι)
    (i : ι) (hinter : binaryWordSupport z ∩ binaryWordSupport z' = {i}) :
    coordinatePhase r z * coordinatePhase r z' =
      coordinatePhase r (z + z') * (r i * r i) := by
  classical
  have hi : i ∈ binaryWordSupport z ∩ binaryWordSupport z' := by
    rw [hinter]
    exact Finset.mem_singleton_self i
  have hzi : z i = 1 := (binary_eq_zero_or_one (z i)).resolve_left
    (coord_mem_support.mp (Finset.mem_inter.mp hi).1)
  have hzi' : z' i = 1 := (binary_eq_zero_or_one (z' i)).resolve_left
    (coord_mem_support.mp (Finset.mem_inter.mp hi).2)
  rw [coordinatePhase_eq_prod, coordinatePhase_eq_prod, coordinatePhase_eq_prod]
  rw [← show (∏ j, if j = i then r j * r j else 1) = r i * r i by simp]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  change (if z j ≠ 0 then r j else 1) * (if z' j ≠ 0 then r j else 1) =
    (if z j + z' j ≠ 0 then r j else 1) * (if j = i then r j * r j else 1)
  by_cases hji : j = i
  · subst j
    simp [hzi, hzi', show (1 + 1 : ZMod 2) = 0 by decide]
  · rcases binary_eq_zero_or_one (z j) with hz | hz <;>
      rcases binary_eq_zero_or_one (z' j) with hz' | hz' <;> simp [hji, hz, hz']
    exfalso
    apply hji
    have hj : j ∈ binaryWordSupport z ∩ binaryWordSupport z' :=
      Finset.mem_inter.mpr ⟨coord_mem_support.mpr (by simp [hz]),
        coord_mem_support.mpr (by simp [hz'])⟩
    rw [hinter] at hj
    exact Finset.mem_singleton.mp hj

/-- If the product phase is one on an additive code, these two witnesses
force the one shared factor to have order at most two. -/
theorem coordinatePhase_square_eq_one_of_single_intersection
    (L : Submodule (ZMod 2) (BinaryWord ι)) (r : ι → G)
    (hOne : ∀ z ∈ L, coordinatePhase r z = 1)
    (z z' : BinaryWord ι) (hz : z ∈ L) (hz' : z' ∈ L)
    (i : ι) (hinter : binaryWordSupport z ∩ binaryWordSupport z' = {i}) :
    r i * r i = 1 := by
  have h := coordinatePhase_mul_of_single_intersection r z z' i hinter
  rw [hOne z hz, hOne z' hz', hOne (z + z') (L.add_mem hz hz'), one_mul, one_mul] at h
  exact h.symm

private theorem wordWeight_eq_binaryWordSupport_card (z : BinaryWord ι) :
    wordWeight z = (binaryWordSupport z).card := by
  simp [wordWeight, binaryWordSupport]

/-- The row-space distance bound supplies two kernel words whose only
common active bit is the prescribed coordinate. -/
theorem exists_kernel_words_single_intersection {b : ℕ}
    (B : Matrix (Fin b) ι (ZMod 2))
    (hRows : Function.Injective (fun a : Fin b → ZMod 2 => a ᵥ* B))
    (hDist : ∀ w : BinaryWord ι, w ≠ 0 →
      (∃ a : Fin b → ZMod 2, a ᵥ* B = w) → b + 1 < wordWeight w)
    (i : ι) :
    ∃ z z' : BinaryWord ι, B *ᵥ z = 0 ∧ B *ᵥ z' = 0 ∧
      binaryWordSupport z ∩ binaryWordSupport z' = {i} := by
  classical
  obtain ⟨a, _, haWeight, hza, hia⟩ :=
    exists_sparse_kernel_word B {i} hRows
      (fun w hw hrow => (by simp : ({i} : Finset ι).card ≤ b + 1).trans_lt (hDist w hw hrow))
      i (Finset.mem_singleton_self i)
  let z : BinaryWord ι := Pi.single i 1 + a
  have hi : i ∈ binaryWordSupport z := coord_mem_support.mpr (by simp [z, hia])
  have hSub : binaryWordSupport z ⊆ insert i (binaryWordSupport a) := by
    intro j hj
    by_cases h : j = i
    · exact Finset.mem_insert.mpr (Or.inl h)
    · have hza' : z j = a j := by simp [z, Pi.single_eq_of_ne h]
      rw [coord_mem_support, hza'] at hj
      exact Finset.mem_insert_of_mem (coord_mem_support.mpr hj)
  have hzCard : (binaryWordSupport z).card ≤ b + 1 := by
    calc
      _ ≤ (insert i (binaryWordSupport a)).card := Finset.card_le_card hSub
      _ ≤ (binaryWordSupport a).card + 1 := Finset.card_insert_le _ _
      _ ≤ b + 1 := by
        rw [← wordWeight_eq_binaryWordSupport_card]
        exact Nat.add_le_add_right haWeight 1
  obtain ⟨a', ha', _, hza', hia'⟩ :=
    exists_sparse_kernel_word B (binaryWordSupport z) hRows
      (fun w hw hrow => hzCard.trans_lt (hDist w hw hrow)) i hi
  let z' : BinaryWord ι := Pi.single i 1 + a'
  refine ⟨z, z', hza, hza', ?_⟩
  ext j
  constructor
  · intro hj
    obtain ⟨hjz, hjz'⟩ := Finset.mem_inter.mp hj
    apply Finset.mem_singleton.mpr
    by_contra h
    have hz' : z' j = 0 := by simp [z', Pi.single_eq_of_ne h, ha' j hjz]
    exact (coord_mem_support.mp hjz') hz'
  · intro hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact Finset.mem_inter.mpr ⟨hi, coord_mem_support.mpr (by simp [z', hia'])⟩

/-- A coordinate-product phase trivial on the check kernel has sign-valued
coordinate factors under the row-space distance condition. -/
theorem coordinatePhase_square_eq_one_of_rowDistance {b : ℕ}
    (B : Matrix (Fin b) ι (ZMod 2))
    (hRows : Function.Injective (fun a : Fin b → ZMod 2 => a ᵥ* B))
    (hDist : ∀ w : BinaryWord ι, w ≠ 0 →
      (∃ a : Fin b → ZMod 2, a ᵥ* B = w) → b + 1 < wordWeight w)
    (r : ι → G) (hOne : ∀ z, B *ᵥ z = 0 → coordinatePhase r z = 1)
    (i : ι) : r i * r i = 1 := by
  obtain ⟨z, z', hz, hz', hInter⟩ := exists_kernel_words_single_intersection B hRows hDist i
  exact coordinatePhase_square_eq_one_of_single_intersection B.mulVecLin.ker r
    (fun z hz => hOne z (LinearMap.mem_ker.mp hz)) z z'
    (LinearMap.mem_ker.mpr hz) (LinearMap.mem_ker.mpr hz') i hInter

#print axioms coordinatePhase_square_eq_one_of_single_intersection
#print axioms exists_kernel_words_single_intersection
#print axioms coordinatePhase_square_eq_one_of_rowDistance

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
