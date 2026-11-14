import CSSPermutationRigidity

/-!
# Multiplicative finite differences of binary phases

The phase values may lie in any commutative group. If the supports of two
kernel words have only one interacting pair, their mixed difference isolates
that pair. Short coordinate projections extend the resulting equations from
the CSS code's allowed words to the whole binary space.
-/

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

variable {A G : Type*} [AddCommGroup A] [CommGroup G]

/-- The multiplicative difference in direction a. -/
def phaseDifference (a : A) (u : A → G) (x : A) : G :=
  u (x + a) / u x

@[simp] theorem phaseDifference_zero (u : A → G) (x : A) :
    phaseDifference 0 u x = 1 := by simp [phaseDifference]

theorem phaseDifference_add (a b : A) (u : A → G) (x : A) :
    phaseDifference (a + b) u x = phaseDifference a u x * phaseDifference b u (x + a) := by
  unfold phaseDifference
  rw [← add_assoc]
  exact (div_mul_div_cancel' _ _ _).symm

theorem phaseDifference_mul (a : A) (u v : A → G) (x : A) :
    phaseDifference a (fun y => u y * v y) x =
      phaseDifference a u x * phaseDifference a v x := by
  unfold phaseDifference
  exact (div_mul_div_comm (u (x + a)) (u x) (v (x + a)) (v x)).symm

theorem phaseDifference_comm (a b : A) (u : A → G) (x : A) :
    phaseDifference a (phaseDifference b u) x = phaseDifference b (phaseDifference a u) x := by
  unfold phaseDifference
  rw [show x + a + b = x + b + a by abel]
  exact div_div_div_comm (u (x + b + a)) (u (x + a)) (u (x + b)) (u x)

/-- A finite sum of directions has trivial difference if each constituent
direction has trivial difference at every translate. -/
theorem phaseDifference_sum_eq_one {ι : Type*} (s : Finset ι) (d : ι → A) (u : A → G)
    (h : ∀ i ∈ s, ∀ x, phaseDifference (d i) u x = 1) :
    ∀ x, phaseDifference (∑ i ∈ s, d i) u x = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    intro x
    rw [Finset.sum_insert hi, phaseDifference_add,
      h i (Finset.mem_insert_self i s), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    exact one_mul 1

/-- If one direction is chosen first and all other directions are trivial
for every translate, a finite sum has the difference of that one direction. -/
theorem phaseDifference_sum_eq_single {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → A) (u : A → G) (i : ι) (hi : i ∈ s)
    (h : ∀ j ∈ s, j ≠ i → ∀ x, phaseDifference (d j) u x = 1) (x : A) :
    phaseDifference (∑ j ∈ s, d j) u x = phaseDifference (d i) u x := by
  have hs : insert i (s.erase i) = s := Finset.insert_erase hi
  rw [← hs, Finset.sum_insert (Finset.notMem_erase _ _), phaseDifference_add]
  rw [phaseDifference_sum_eq_one _ _ _
    (fun j hj => h j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)), mul_one]

/-- Two finite sums whose constituent mixed differences are all trivial
have trivial mixed difference. -/
theorem phaseDifference_sums_eq_one {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (d : ι → A) (e : κ → A) (u : A → G)
    (h : ∀ i ∈ s, ∀ j ∈ t, ∀ x, phaseDifference (d i) (phaseDifference (e j) u) x = 1)
    (x : A) :
    phaseDifference (∑ i ∈ s, d i) (phaseDifference (∑ j ∈ t, e j) u) x = 1 := by
  apply phaseDifference_sum_eq_one
  intro i hi y
  rw [phaseDifference_comm]
  apply phaseDifference_sum_eq_one
  exact fun j hj z => (phaseDifference_comm (e j) (d i) u z).trans (h i hi j hj z)

/-- Only one mixed pair need be retained if the others are trivial. Ordering
the chosen directions first in each sum evaluates it at the original point. -/
theorem phaseDifference_sums_eq_single_pair {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (d : ι → A) (e : κ → A) (u : A → G)
    (i₀ : ι) (j₀ : κ) (hi₀ : i₀ ∈ s) (hj₀ : j₀ ∈ t)
    (h : ∀ i ∈ s, ∀ j ∈ t, (i ≠ i₀ ∨ j ≠ j₀) → ∀ x,
      phaseDifference (d i) (phaseDifference (e j) u) x = 1) (x : A) :
    phaseDifference (∑ i ∈ s, d i) (phaseDifference (∑ j ∈ t, e j) u) x =
      phaseDifference (d i₀) (phaseDifference (e j₀) u) x := by
  rw [phaseDifference_sum_eq_single s d _ i₀ hi₀]
  · rw [phaseDifference_comm (d i₀) (∑ j ∈ t, e j),
      phaseDifference_sum_eq_single t e _ j₀ hj₀, phaseDifference_comm (e j₀) (d i₀)]
    exact fun j hj hne z => (phaseDifference_comm (e j) (d i₀) u z).trans
      (h i₀ hi₀ j hj (Or.inr hne) z)
  · intro i hi hne y
    rw [phaseDifference_comm]
    apply phaseDifference_sum_eq_one
    exact fun j hj z => (phaseDifference_comm (e j) (d i) u z).trans (h i hi j hj (Or.inl hne) z)

section Binary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support of a binary word, with nonzero entries equal to one. -/
def binaryWordSupport (z : BinaryWord ι) : Finset ι :=
  Finset.univ.filter fun i => z i ≠ 0

theorem sum_basis_on_binaryWordSupport (z : BinaryWord ι) :
    (∑ i ∈ binaryWordSupport z, (Pi.single i 1 : BinaryWord ι)) = z := by
  classical
  funext j
  rw [Finset.sum_apply]
  by_cases hj : j ∈ binaryWordSupport z
  · rw [Finset.sum_eq_single_of_mem j hj, Pi.single_eq_same]
    · have hn : z j ≠ 0 := (Finset.mem_filter.mp hj).2
      have hv := (z j).val_lt
      have hval : (z j).val = 1 := by
        by_contra hne
        have hz : (z j).val = 0 := by omega
        exact hn ((ZMod.val_eq_zero _).mp hz)
      exact ((ZMod.val_eq_one (by decide) _).mp hval).symm
    · intro i _ hne
      exact Pi.single_eq_of_ne hne.symm _
  · have hz : z j = 0 := by simpa [binaryWordSupport] using hj
    rw [hz]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : j ≠ i := fun hij => hj (hij ▸ hi)
    exact Pi.single_eq_of_ne hne _

/-- For a phase constant on the allowed words, two allowed kernel shifts
with only one interacting pair force that pair's mixed difference to be
trivial on the allowed words. -/
theorem mixed_bitDifference_eq_one_of_isolating_words
    (L : Submodule (ZMod 2) (BinaryWord ι)) (u : BinaryWord ι → G)
    (hu : ∀ x ∈ L, u x = 1) (z z' : BinaryWord ι) (hz : z ∈ L) (hz' : z' ∈ L)
    (i j : ι) (hi : i ∈ binaryWordSupport z) (hj : j ∈ binaryWordSupport z')
    (hTrivial : ∀ a ∈ binaryWordSupport z, ∀ b ∈ binaryWordSupport z',
      (a ≠ i ∨ b ≠ j) → ∀ x,
      phaseDifference (Pi.single a 1 : BinaryWord ι)
        (phaseDifference (Pi.single b 1 : BinaryWord ι) u) x = 1)
    (x : BinaryWord ι) (hx : x ∈ L) :
    phaseDifference (Pi.single i 1 : BinaryWord ι)
      (phaseDifference (Pi.single j 1 : BinaryWord ι) u) x = 1 := by
  have h := phaseDifference_sums_eq_single_pair (binaryWordSupport z) (binaryWordSupport z')
    (fun a => (Pi.single a 1 : BinaryWord ι)) (fun b => (Pi.single b 1 : BinaryWord ι))
    u i j hi hj hTrivial x
  rw [sum_basis_on_binaryWordSupport z, sum_basis_on_binaryWordSupport z'] at h
  rw [← h]
  simp [phaseDifference, hu x hx, hu (x + z) (L.add_mem hx hz),
    hu (x + z') (L.add_mem hx hz'), hu (x + z + z') (L.add_mem (L.add_mem hx hz) hz')]

omit [Fintype ι] [DecidableEq ι] in
/-- A mixed phase difference invariant under a projecting subspace is
constant on all words. -/
theorem phase_constant_of_translation_invariant_on_projecting_space
    {H : Submodule (ZMod 2) (BinaryWord ι)} {r : ℕ} {S : Finset ι}
    (hH : HasProjection H r) (hS : S.card ≤ r)
    {u : BinaryWord ι → G} (hdep : DependsOn S u)
    (hInv : ∀ a ∈ H, ∀ x, phaseDifference a u x = 1) (x : BinaryWord ι) :
    u x = u 0 := by
  obtain ⟨a, ha, hax⟩ := hH S hS x
  exact (hdep a x hax).symm.trans (by
    simpa only [phaseDifference, zero_add, div_eq_one] using hInv a ha 0)

/-- If a direction is an involution, its constant multiplicative difference
has order at most two. -/
theorem square_eq_one_of_constant_phaseDifference {a : A}
    (ha : a + a = 0) (u : A → G) (c : G)
    (h : ∀ x, phaseDifference a u x = c) : c * c = 1 := by
  have hstep := phaseDifference_add a a u 0
  rw [ha, phaseDifference_zero, h, h] at hstep
  exact hstep.symm

end Binary

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
