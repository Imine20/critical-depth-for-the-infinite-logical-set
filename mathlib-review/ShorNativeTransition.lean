import ShorNativeTransitionArity

/-!
A Shor support transition admits a physical native layer with one
controlled-addition block per active pivot.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript

theorem exists_native_transition_layer {n : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (A A' D D' : Finset (Fin n))
    (hAA' : A ⊆ A') (hD'D : D' ⊆ D) (hA'D : Disjoint A' D)
    (hA' : A'.card = A.card * q) (hD : D.card = D'.card * q) :
    ∃ (parent : Fin n → Option (Fin n))
      (huntouched : ∀ i a, parent i = some a → parent a = none)
      (harity : ∀ a, (parentSites parent a).card ≤ q)
      (L : ArbitraryLayer n (fun _ => 2) q),
      L = nativeParentLayer parent huntouched harity ∧
      fanout parent (mark A) = mark A' ∧ fanout parent (mark D) = mark D' := by
  obtain ⟨eA, eD, huntouched, hA, hD'⟩ :=
    exists_fanout_transition q hq A A' D D' hAA' hD'D hA'D hA' hD
  let harity := transitionParent_arity q hq A A' D D' hAA' hD'D hA'D eA eD
  exact ⟨_, huntouched, harity, nativeParentLayer _ huntouched harity, rfl, hA, hD'⟩

#print axioms exists_native_transition_layer

end CriticalDepth.FaultShorSaturation