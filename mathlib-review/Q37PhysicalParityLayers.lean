import Q37NativeBlocks
import Q37ConjugatedParityLayer

/-!
# Physical parity matrices for the two registered Q37 block families
-/

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation

noncomputable def q37ParityLayer (z : Circle) : Layer 37 (fun _ => 2) 3 :=
  (parityPhaseLayer z q37ParitySupports q37ParitySupports_pairwise).normalized

noncomputable def q37LineLayerInBasis (z : Circle) (v : Fin 37 → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) : Layer 37 (fun _ => 2) 3 :=
  (conjugateNativeLayer v hv (parityPhaseLayer z q37LineSupports
    q37LineSupports_pairwise)).normalized

theorem q37ParityLayer_eval (z : Circle) :
    (q37ParityLayer z).eval = Matrix.diagonal (fun x => (z : ℂ) ^ countOddBlocks q37ParitySupports x) :=
  parityPhaseLayer_normalized_eval z q37ParitySupports q37ParitySupports_pairwise
    q37ParitySupports_nonempty

theorem q37LineLayerInBasis_eval (z : Circle) (v : Fin 37 → Operator (Fin 2))
    (hv : ∀ i, IsUnitary (v i)) :
    (q37LineLayerInBasis z v hv).eval = tensorEntries v *
      Matrix.diagonal (fun x => (z : ℂ) ^ countOddBlocks q37LineSupports x) *
        (tensorEntries v).conjTranspose :=
  conjugateParityPhaseLayer_normalized_eval z q37LineSupports q37LineSupports_pairwise
    q37LineSupports_nonempty v hv

#print axioms q37ParityLayer_eval
#print axioms q37LineLayerInBasis_eval

end CriticalDepth.Q37BinaryData
