import CSSMonomialPhaseLocality

/-!
Turn the individual light-cone supports into the interaction graph
used by the CSS rigidity proof.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Type*} [CommGroup G]

noncomputable def phaseNeighbors (u : BinaryWord ι → G) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun j => i ≠ j ∧ ∃ x, mixedBitPhaseDifference u i j x ≠ 1

theorem phaseNeighbors_mem_iff (u : BinaryWord ι → G) (i j : ι) :
    j ∈ phaseNeighbors u i ↔ i ≠ j ∧ ∃ x, mixedBitPhaseDifference u i j x ≠ 1 := by
  classical
  unfold phaseNeighbors
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem phaseNeighbors_symm (u : BinaryWord ι → G) (i j : ι) :
    i ∈ phaseNeighbors u j ↔ j ∈ phaseNeighbors u i := by
  classical
  rw [phaseNeighbors_mem_iff, phaseNeighbors_mem_iff]
  rw [ne_comm]
  constructor <;> rintro ⟨hne, x, hx⟩
  · exact ⟨hne, x, fun h => hx ((mixedBitPhaseDifference_comm u j i x).trans h)⟩
  · exact ⟨hne, x, fun h => hx ((mixedBitPhaseDifference_comm u i j x).trans h)⟩

theorem phaseNeighbors_le_of_dependence (u : BinaryWord ι → G) (i : ι)
    (S : Finset ι) (hS : DependsOn S (bitPhaseDifference u i)) :
    phaseNeighbors u i ⊆ S := by
  classical
  intro j hj
  obtain ⟨_, x, hx⟩ := (phaseNeighbors_mem_iff u i j).mp hj
  by_contra hn
  have hT := hS (x + Pi.single j 1) x (fun k hk => by
    have hk' : k ≠ j := fun h => hn (h ▸ hk)
    simp [Pi.single_eq_of_ne hk'])
  apply hx
  rw [mixedBitPhaseDifference_comm u i j]
  change phaseDifference (Pi.single j 1) (bitPhaseDifference u i) x = 1
  rw [phaseDifference, hT, div_self']

theorem mixedBitPhaseDifference_dependsOn_first (u : BinaryWord ι → G) (i j : ι)
    (S : Finset ι) (hS : DependsOn S (bitPhaseDifference u i)) :
    DependsOn S (mixedBitPhaseDifference u i j) := by
  intro x y hxy
  calc
    mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u j i x :=
      mixedBitPhaseDifference_comm u i j x
    _ = mixedBitPhaseDifference u j i y := by
      change phaseDifference (Pi.single j 1) (bitPhaseDifference u i) x =
        phaseDifference (Pi.single j 1) (bitPhaseDifference u i) y
      unfold phaseDifference
      rw [hS x y hxy, hS (x + Pi.single j 1) (y + Pi.single j 1)
        (fun k hk => by simp only [Pi.add_apply, hxy k hk])]
    _ = mixedBitPhaseDifference u i j y :=
      mixedBitPhaseDifference_comm u j i y

/-- The bad interactions can be isolated in the row-matrix kernel.
Combining this with short projection yields the constant mixed differences. -/
theorem mixedBitPhaseDifference_constant_of_short_light_cones
    {b : ℕ} (H L : Submodule (ZMod 2) (BinaryWord ι))
    (B : Matrix (Fin b) ι (ZMod 2))
    (hRows : Function.Injective (fun a : Fin b → ZMod 2 => a ᵥ* B))
    (hKernel : ∀ x : BinaryWord ι, B *ᵥ x = 0 → x ∈ L)
    (R T : ℕ) (hT₁ : R + 2 ≤ T) (hT₂ : 1 + (b + 1) * (R + 1) ≤ T)
    (hDist : ∀ w : BinaryWord ι, w ≠ 0 → (∃ a : Fin b → ZMod 2, a ᵥ* B = w) →
      T < wordWeight w)
    (u : BinaryWord ι → G)
    (hH : HasProjection H R) (hL : HasProjection L R)
    (hInv : ∀ a ∈ H, ∀ x ∈ L, phaseDifference a u x = 1)
    (hLocal : ∀ i, ∃ S : Finset ι, S.card ≤ R ∧ DependsOn S (bitPhaseDifference u i)) :
    ∀ i j, i ≠ j → ∀ x, mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0 := by
  classical
  have hg (i : ι) : (phaseNeighbors u i).card ≤ R := by
    obtain ⟨s, hs, hd⟩ := hLocal i
    exact (Finset.card_le_card (phaseNeighbors_le_of_dependence u i s hd)).trans hs
  apply mixedBitPhaseDifference_constant_of_isolation H L R u hH hL hInv
  · intro i j _
    obtain ⟨s, hs, hd⟩ := hLocal i
    exact ⟨s, hs, mixedBitPhaseDifference_dependsOn_first u i j s hd⟩
  · intro i j hij _
    obtain ⟨z, z', hz, hz', hi, hj, hd, he⟩ := exists_isolating_kernel_shifts
      B hRows T R hT₁ hT₂ hDist (phaseNeighbors u) hg (phaseNeighbors_symm u) i j hij
    refine ⟨z, hKernel z hz, z', hKernel z' hz', hi, hj, ?_⟩
    intro k hk l hl hn x
    by_contra hx
    have hkl : k ≠ l := fun h => Finset.disjoint_left.mp hd hk (h.symm ▸ hl)
    have hl' : l ∈ phaseNeighbors u k :=
      (phaseNeighbors_mem_iff u k l).mpr ⟨hkl, x, hx⟩
    obtain ⟨hk', hl''⟩ := he k hk l hl hl'
    exact hn.elim (fun h => h hk') (fun h => h hl'')

#print axioms mixedBitPhaseDifference_constant_of_short_light_cones

end CriticalDepth.Manuscript20261114.CSSCheckSpaces