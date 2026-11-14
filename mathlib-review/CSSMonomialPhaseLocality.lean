import CSSIsolatingShifts
import CSSMonomialLocality

/-!
# Light-cone locality of phase differences

When the binary permutation is a translation, a conjugated single-bit X
test still flips that bit on every basis line. Therefore its support
contains the bit and controls the whole phase difference.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.FaultCircuitSupport Matrix

variable {n : ℕ}

theorem monomial_translate_phaseDifference_dependsOn
    {U : Operator (QubitBasis n)} (hu : IsUnitary U)
    {f : Equiv.Perm (BinaryWord (Fin n))} {u : BinaryWord (Fin n) → ℂˣ}
    (hm : binaryMonomial U f u) (translation : BinaryWord (Fin n))
    (hf : ∀ x, f x = x + translation)
    (i : Fin n) (S : Finset (Fin n))
    (hs : SupportedOn (propagate U (pauliMatrix 0 (singleSitePauli i .X))) S) :
    i ∈ S ∧ DependsOn S (bitPhaseDifference u i) := by
  classical
  let t : BinaryWord (Fin n) := Pi.single i 1
  let A := propagate U (pauliMatrix 0 (singleSitePauli i .X))
  let e := binaryWordEquiv n
  have hphase (x : BinaryWord (Fin n)) :
      A (e.symm (f (x + t))) (e.symm (f x)) =
        ((bitPhaseDifference u i x : ℂˣ) : ℂ) := by
    have he := monomial_conjugate_entry U hu f u hm (pauliMatrix 0 (singleSitePauli i .X)) (x + t) x
    rw [pauli_singleX_binary_entry, if_pos (rfl : x + t = x + Pi.single i 1), mul_one] at he
    change A (e.symm (f (x + t))) (e.symm (f x)) * (u x : ℂ) = (u (x + t) : ℂ) at he
    rw [bitPhaseDifference, phaseDifference]
    change _ = ((u (x + t) / u x : ℂˣ) : ℂ)
    rw [Units.val_div_eq_div_val]
    exact (eq_div_iff (Units.ne_zero (u x))).2 he
  have hZ (x : BinaryWord (Fin n)) (j : Fin n) :
      f (x + t) j = (x j + t j) + translation j := by
    simp only [hf, Pi.add_apply]
  obtain ⟨B, hB⟩ := hs
  change A = localEmbed S B at hB
  have hin : i ∈ S := by
    by_contra hi
    have hn : e.symm (f (0 + t)) i ≠ e.symm (f 0) i := by
      apply qubitBitEquiv.symm.injective.ne
      change f (0 + t) i ≠ f 0 i
      rw [hf, hf]
      simp [t, Pi.add_apply]
    have hzero : A (e.symm (f (0 + t))) (e.symm (f 0)) = 0 := by
      rw [hB]
      unfold localEmbed
      exact if_neg fun h => hn (h i hi)
    rw [hphase] at hzero
    exact Units.ne_zero _ hzero
  refine ⟨hin, ?_⟩
  intro x y hxy
  have hentry (x : BinaryWord (Fin n)) :
      A (e.symm (f (x + t))) (e.symm (f x)) =
        B (fun j => e.symm (f (x + t)) j.val) (fun j => e.symm (f x) j.val) := by
    rw [hB]
    unfold localEmbed
    apply if_pos
    intro j hj
    apply congrArg qubitBitEquiv.symm
    change f (x + t) j = f x j
    have hji : j ≠ i := fun hh => hj (hh ▸ hin)
    simp [hf, t, hji]
  apply Units.ext
  rw [← hphase, ← hphase, hentry, hentry]
  have hx' : (fun j : S => e.symm (f (x + t)) j.val) =
      fun j : S => e.symm (f (y + t)) j.val := by
    funext j
    apply congrArg qubitBitEquiv.symm
    change f (x + t) j.val = f (y + t) j.val
    rw [hZ, hZ, hxy _ j.property]
  have hy' : (fun j : S => e.symm (f x) j.val) = fun j : S => e.symm (f y) j.val := by
    funext j
    apply congrArg qubitBitEquiv.symm
    change f x j.val = f y j.val
    simp [hf, hxy _ j.property]
  rw [hx', hy']

/-- A mixed derivative can only use neighbors already in its first
coordinate's support. -/
theorem bitPhase_nontrivial_neighbors_subset
    (u : BinaryWord (Fin n) → ℂˣ) (i : Fin n) (S : Finset (Fin n))
    (hs : DependsOn S (bitPhaseDifference u i)) (j : Fin n)
    (hnon : ∃ x, mixedBitPhaseDifference u j i x ≠ 1) :
    j ∈ S := by
  by_contra hn
  obtain ⟨x, hx⟩ := hnon
  have he : bitPhaseDifference u i (x + Pi.single j 1) = bitPhaseDifference u i x := by
    apply hs
    intro k hk
    have hkj : k ≠ j := fun h => hn (h ▸ hk)
    simp [Pi.single_eq_of_ne hkj]
  apply hx
  change phaseDifference (Pi.single j 1) (bitPhaseDifference u i) x = 1
  simp [phaseDifference, he]

#print axioms monomial_translate_phaseDifference_dependsOn
#print axioms bitPhase_nontrivial_neighbors_subset

end CriticalDepth.Manuscript20261114.CSSCheckSpaces