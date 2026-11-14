import Q37BinaryData
import Q37NativeParityLayer
import Mathlib.Data.Nat.Bitwise

/-!
# The physical supports for the two Q37 native parity layers
-/

open scoped BigOperators

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation

/-- The sites selected by a binary mask. -/
def sitesOfNatMask (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => k.testBit i.val

/-- The corresponding word in the binary field. -/
def wordOfNatMask (n k : ℕ) : Fin n → Bit :=
  fun i => if k.testBit i.val then 1 else 0

theorem wordOfNatMask_xor (n a b : ℕ) :
    wordOfNatMask n (Nat.xor a b) = wordOfNatMask n a + wordOfNatMask n b := by
  funext i
  change (if (a ^^^ b).testBit i.val then (1 : Bit) else 0) =
    (if a.testBit i.val then 1 else 0) + (if b.testBit i.val then 1 else 0)
  rw [Nat.testBit_xor]
  cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;>
    simp [ha, hb, show (1 : Bit) + 1 = 0 by decide]

theorem weight_eq_sum_bits (n k : ℕ) :
    weight n k = ∑ i : Fin n, (k.testBit i.val).toNat := by
  unfold weight
  have hfold (L : List ℕ) (a : ℕ) :
      L.foldl (fun t i => t + (k.testBit i).toNat) a =
        a + (L.map fun i => (k.testBit i).toNat).sum := by
    induction L generalizing a with
    | nil => simp
    | cons i L ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, Nat.add_assoc]
  rw [hfold, zero_add]
  have hList : List.range n = List.ofFn (fun i : Fin n => i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi h'i
      simp
  rw [hList, List.map_ofFn, List.sum_ofFn]
  rfl

theorem card_sitesOfNatMask (n k : ℕ) : (sitesOfNatMask n k).card = weight n k := by
  rw [weight_eq_sum_bits]
  classical
  rw [sitesOfNatMask, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases k.testBit i.val <;> rfl

/-- Pairwise disjoint bit masks in the certificate give disjoint genuine
physical site supports. -/
theorem disjoint_sitesOfNatMask_of_land_zero (n a b : ℕ)
    (hab : Nat.land a b = 0) : Disjoint (sitesOfNatMask n a) (sitesOfNatMask n b) := by
  apply Finset.disjoint_left.mpr
  intro i ha hb
  have h1 := (Finset.mem_filter.mp ha).2
  have h2 := (Finset.mem_filter.mp hb).2
  have h := congrArg (fun v : ℕ => v.testBit i.val) hab
  change (a &&& b).testBit i.val = (0 : ℕ).testBit i.val at h
  rw [Nat.testBit_land, h1, h2] at h
  simpa using h

/-- The certificate's binary dot product is the phase control bit of
the corresponding gate and physical computational word. -/
theorem blockOdd_wordOfNatMask (a b : ℕ) :
    blockOdd (sitesOfNatMask 37 a) ((binaryWordEquiv 37).symm (wordOfNatMask 37 b)) =
      decide (dot a b = 1) := by
  unfold blockOdd dot
  rw [(binaryWordEquiv 37).apply_symm_apply, weight_eq_sum_bits]
  have hsum :
      (∑ i ∈ sitesOfNatMask 37 a, wordOfNatMask 37 b i) =
        ((∑ i : Fin 37, ((a &&& b).testBit i.val).toNat : ℕ) : Bit) := by
    rw [Nat.cast_sum, sitesOfNatMask, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.testBit_land]
    cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;>
      simp [ha, hb, wordOfNatMask]
  rw [hsum]
  have h : ((∑ i : Fin 37, ((a &&& b).testBit i.val).toNat : ℕ) : Bit) = 1 ↔
      (∑ i : Fin 37, ((a &&& b).testBit i.val).toNat) % 2 = 1 := by
    rw [← ZMod.val_eq_one (by decide), ZMod.val_natCast]
  simp only [h]
  rfl

def paritySupport (a : {a : ℕ // a ∈ parityBlocks}) :
    {S : Finset (Fin 37) // S.card ≤ 3} :=
  ⟨sitesOfNatMask 37 a.val, by
    rw [card_sitesOfNatMask]
    have h := List.all_eq_true.mp gate_partition_certificate.2.2.1 a.val a.property
    exact of_decide_eq_true h⟩

def lineSupport (a : {a : ℕ // a ∈ lineBlocks}) :
    {S : Finset (Fin 37) // S.card ≤ 3} :=
  ⟨sitesOfNatMask 37 a.val, by
    rw [card_sitesOfNatMask]
    have h := List.all_eq_true.mp gate_partition_certificate.2.2.2.1 a.val a.property
    exact le_of_eq (beq_iff_eq.mp h)⟩

def q37ParitySupports : List {S : Finset (Fin 37) // S.card ≤ 3} :=
  parityBlocks.attach.map paritySupport

def q37LineSupports : List {S : Finset (Fin 37) // S.card ≤ 3} :=
  lineBlocks.attach.map lineSupport

private theorem pairwise_land_eq_zero_of_mutuallyDisjoint {L : List ℕ}
    (hL : mutuallyDisjoint L = true) : L.Pairwise fun a b => Nat.land a b = 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [mutuallyDisjoint, Bool.and_eq_true] at hL
    exact List.pairwise_cons.mpr ⟨fun b hb => beq_iff_eq.mp (List.all_eq_true.mp hL.1 b hb),
      ih hL.2⟩

theorem q37ParitySupports_pairwise :
    q37ParitySupports.Pairwise fun A B => Disjoint A.val B.val := by
  unfold q37ParitySupports
  rw [List.pairwise_map]
  have h := pairwise_land_eq_zero_of_mutuallyDisjoint gate_partition_certificate.1
  rw [← List.attach_map_subtype_val parityBlocks, List.pairwise_map] at h
  exact h.imp (fun {a b} ha => disjoint_sitesOfNatMask_of_land_zero 37 a.val b.val ha)

theorem q37LineSupports_pairwise :
    q37LineSupports.Pairwise fun A B => Disjoint A.val B.val := by
  unfold q37LineSupports
  rw [List.pairwise_map]
  have h := pairwise_land_eq_zero_of_mutuallyDisjoint gate_partition_certificate.2.1
  rw [← List.attach_map_subtype_val lineBlocks, List.pairwise_map] at h
  exact h.imp (fun {a b} ha => disjoint_sitesOfNatMask_of_land_zero 37 a.val b.val ha)

theorem q37ParitySupports_nonempty : ∀ S ∈ q37ParitySupports, S.val.Nonempty := by
  intro S hS
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hS
  apply Finset.card_pos.mp
  change 0 < (sitesOfNatMask 37 a.val).card
  rw [card_sitesOfNatMask]
  exact of_decide_eq_true (List.all_eq_true.mp
    (show parityBlocks.all (fun a => decide (0 < weight 37 a)) = true by decide) _ a.property)

theorem q37LineSupports_nonempty : ∀ S ∈ q37LineSupports, S.val.Nonempty := by
  intro S hS
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hS
  apply Finset.card_pos.mp
  change 0 < (sitesOfNatMask 37 a.val).card
  rw [card_sitesOfNatMask]
  have h := List.all_eq_true.mp gate_partition_certificate.2.2.2.1 a.val a.property
  rw [beq_iff_eq.mp h]
  decide

#print axioms card_sitesOfNatMask
#print axioms blockOdd_wordOfNatMask
#print axioms q37ParitySupports_pairwise
#print axioms q37LineSupports_pairwise

end CriticalDepth.Q37BinaryData
