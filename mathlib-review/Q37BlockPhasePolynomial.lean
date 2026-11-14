import Q37ParityPolynomial
import Q37BinaryData

/-!
Parities of the two constant-size physical block patterns of Q37.
-/

namespace CriticalDepth.Q37BinaryData

open scoped BigOperators

def blockCoefficients (checks blocks : List Nat)
    (j : Fin blocks.length) : Finset (Fin checks.length) :=
  Finset.univ.filter fun i => dot checks[i] blocks[j] = 1

def shiftedBlockSign (logical : ℕ) (blocks : List Nat) (j : Fin blocks.length) : ℤ :=
  if dot logical blocks[j] = 0 then 1 else -1

def shiftedBlockOffset (logical : ℕ) (blocks : List Nat) : ℤ :=
  ∑ j : Fin blocks.length, (dot logical blocks[j] : ℤ)

def blockPhaseSum (checks blocks : List Nat) (logical : ℕ) (r : ℕ)
    (mask : Finset (Fin checks.length)) : ZMod (2 ^ r) :=
  (shiftedBlockOffset logical blocks : ZMod (2 ^ r)) +
  ∑ j : Fin blocks.length,
    (shiftedBlockSign logical blocks j : ZMod (2 ^ r)) *
      (supportParity (blockCoefficients checks blocks j) mask : ZMod (2 ^ r))

theorem blockPhaseSum_of_small_masks (checks blocks : List Nat) (logical r : ℕ)
    (u : ZMod (2 ^ r))
    (hSmall : ∀ s : Finset (Fin checks.length), s.card ≤ r →
      blockPhaseSum checks blocks logical r s = u) (s : Finset (Fin checks.length)) :
    blockPhaseSum checks blocks logical r s = u := by
  let c : ZMod (2 ^ r) := shiftedBlockOffset logical blocks
  have hx (s : Finset (Fin checks.length)) (hs : s.card ≤ r) :
      ∑ j ∈ Finset.univ, (shiftedBlockSign logical blocks j : ZMod (2 ^ r)) *
        (supportParity (blockCoefficients checks blocks j) s : ZMod (2 ^ r)) = u - c := by
    have h := hSmall s hs
    change c + _ = u at h
    exact eq_sub_of_add_eq (by rwa [add_comm] at h)
  have ht := affineParitySum_of_small_masks Finset.univ (blockCoefficients checks blocks)
    (shiftedBlockSign logical blocks) r (u - c) hx s
  unfold blockPhaseSum
  rw [ht, add_sub_cancel]

#print axioms blockPhaseSum_of_small_masks

end CriticalDepth.Q37BinaryData