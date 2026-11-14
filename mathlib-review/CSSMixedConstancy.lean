import CSSPhaseOverlap
import CSSQuadraticPhase

/-!
Local mixed phase differences become constant using the two projecting
check spaces and the sparse words isolating a single interaction.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [CommGroup G]

private theorem phaseDifference_dependsOn {s : Finset ι} {u : BinaryWord ι → G}
    (h : DependsOn s u) (a : BinaryWord ι) :
    DependsOn s (phaseDifference a u) := by
  intro x y hxy
  have hAdd : ∀ i ∈ s, (x + a) i = (y + a) i := by
    intro i hi
    change x i + a i = y i + a i
    rw [hxy i hi]
  unfold phaseDifference
  rw [h (x + a) (y + a) hAdd, h x y hxy]

/-- When two shifts in L isolate each nontrivial interacting pair, every
short mixed difference is constant on the full register. -/
theorem mixedBitPhaseDifference_constant_of_isolation
    (H L : Submodule (ZMod 2) (BinaryWord ι)) (R : ℕ)
    (u : BinaryWord ι → G)
    (hH : HasProjection H R) (hL : HasProjection L R)
    (hInv : ∀ a ∈ H, ∀ x ∈ L, phaseDifference a u x = 1)
    (hlocal : ∀ i j, i ≠ j → ∃ S : Finset ι, S.card ≤ R ∧
      DependsOn S (mixedBitPhaseDifference u i j))
    (hisol : ∀ i j, i ≠ j → (∃ x, mixedBitPhaseDifference u i j x ≠ 1) →
      ∃ z ∈ L, ∃ z' ∈ L, i ∈ binaryWordSupport z ∧ j ∈ binaryWordSupport z' ∧
        ∀ k ∈ binaryWordSupport z, ∀ l ∈ binaryWordSupport z',
          (k ≠ i ∨ l ≠ j) → ∀ x, mixedBitPhaseDifference u k l x = 1) :
    ∀ i j, i ≠ j → ∀ x, mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0 := by
  classical
  intro i j hij
  by_cases hNZ : ∃ x, mixedBitPhaseDifference u i j x ≠ 1
  · obtain ⟨S, hcard, hl⟩ := hlocal i j hij
    obtain ⟨z, hz, z', hz', hi, hj, hother⟩ := hisol i j hij hNZ
    apply phase_constant_of_translation_invariant_on_projecting_space hH hcard hl
    intro a ha x
    have hL' : ∀ v ∈ L, phaseDifference a (mixedBitPhaseDifference u i j) v = 1 := by
      intro v hv
      have hTrivial (k : ι) (hk : k ∈ binaryWordSupport z)
          (l : ι) (hl' : l ∈ binaryWordSupport z') (hn : k ≠ i ∨ l ≠ j) (y : BinaryWord ι) :
          mixedBitPhaseDifference (phaseDifference a u) k l y = 1 := by
        change phaseDifference (Pi.single k 1) (phaseDifference (Pi.single l 1) (phaseDifference a u)) y = 1
        have hcomm : phaseDifference (Pi.single l 1) (phaseDifference a u) =
            phaseDifference a (phaseDifference (Pi.single l 1) u) := by
          funext z
          exact phaseDifference_comm _ _ _ _
        rw [hcomm, phaseDifference_comm (Pi.single k 1) a]
        change phaseDifference a (mixedBitPhaseDifference u k l) y = 1
        simp [phaseDifference, hother k hk l hl' hn]
      have h := mixed_bitDifference_eq_one_of_isolating_words L (phaseDifference a u)
        (hInv a ha) z z' hz hz' i j hi hj hTrivial v hv
      change mixedBitPhaseDifference (phaseDifference a u) i j v = 1 at h
      change phaseDifference (Pi.single i 1) (phaseDifference (Pi.single j 1) (phaseDifference a u)) v = 1 at h
      have hcomm : phaseDifference (Pi.single j 1) (phaseDifference a u) =
          phaseDifference a (phaseDifference (Pi.single j 1) u) := by
        funext z
        exact phaseDifference_comm _ _ _ _
      rwa [hcomm, phaseDifference_comm (Pi.single i 1) a] at h
    obtain ⟨y, hy, hyx⟩ := hL S hcard x
    exact ((phaseDifference_dependsOn hl a) y x hyx).symm.trans (hL' y hy)
  · push Not at hNZ
    intro x
    rw [hNZ x, hNZ 0]

#print axioms mixedBitPhaseDifference_constant_of_isolation

end CriticalDepth.Manuscript20261114.CSSCheckSpaces