import CSSDisjointEquations
import Mathlib.FieldTheory.Finiteness

/-!
# Finite certificate counts for binary check spaces

The counting statements use natural cardinalities. Ratios of these
cardinalities under a uniform finite sample give the corresponding
probability bounds.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators

theorem card_binary_linearMap_kernel_bound {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (F : V →ₗ[ZMod 2] W) (a r : ℕ)
    (hV : Module.finrank (ZMod 2) V = a)
    (hrank : r ≤ Module.finrank (ZMod 2) F.range) :
    Nat.card F.ker ≤ 2 ^ (a - r) := by
  classical
  have hdim := LinearMap.finrank_range_add_finrank_ker F
  rw [hV] at hdim
  letI : Fintype F.ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem card_binary_linearMap_ker_add_range {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (F : V →ₗ[ZMod 2] W) :
    Nat.card F.ker * Nat.card F.range = Fintype.card V := by
  classical
  letI : Fintype F.ker := Fintype.ofFinite _
  letI : Fintype F.range := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := F.ker),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := F.range),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card, ← pow_add,
    add_comm, F.finrank_range_add_finrank_ker]

def wordSupport {n : ℕ} (x : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i ≠ 0

private theorem wordSupport_injective {n : ℕ} :
    Function.Injective (@wordSupport n) := by
  intro x y hxy
  funext i
  have hm : x i ≠ 0 ↔ y i ≠ 0 := by
    simpa only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show (i ∈ wordSupport x) ↔ (i ∈ wordSupport y) from hxy ▸ Iff.rfl)
  have hb (a b : ZMod 2) (h : a ≠ 0 ↔ b ≠ 0) : a = b := by decide +revert
  exact hb _ _ hm

theorem card_binary_weight_shell_le (n k : ℕ) :
    Nat.card {x : Fin n → ZMod 2 // (wordSupport x).card = k} ≤ n.choose k := by
  classical
  let targets := Finset.powersetCard k (Finset.univ : Finset (Fin n))
  let f : {x : Fin n → ZMod 2 // (wordSupport x).card = k} → targets :=
    fun x => ⟨wordSupport x.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, x.property⟩⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (wordSupport_injective (congrArg Subtype.val h))
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := targets), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h

/-- Union bound for finite certificates. The family of bad sets cannot
cover the sample space when the sum of their sizes is smaller. -/
theorem exists_outside_bad_sets {ι α : Type*} [Fintype α] [DecidableEq α]
    (indices : Finset ι) (bad : ι → Finset α)
    (h : (∑ i ∈ indices, (bad i).card) < Fintype.card α) :
    ∃ a : α, ∀ i ∈ indices, a ∉ bad i := by
  let union := indices.biUnion bad
  have hlt : union.card < (Finset.univ : Finset α).card := by
    simpa using (Finset.card_biUnion_le.trans_lt h :
      (indices.biUnion bad).card < Fintype.card α)
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨a, fun i hi hb => ha (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩)⟩

#print axioms card_binary_linearMap_kernel_bound
#print axioms card_binary_weight_shell_le
#print axioms exists_outside_bad_sets

end CriticalDepth.Manuscript20261114.CSSCheckSpaces