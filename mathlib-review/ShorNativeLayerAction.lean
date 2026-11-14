import ShorNativeParallelFanout

/-!
# Physical action of the parallel fanout layer
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

variable {n q : ℕ}

private def wordOfBits (x : Fin n → Bit) : QubitBasis n :=
  fun i => qubitBitEquiv.symm (x i)

private def bitsOfWord (x : QubitBasis n) : Fin n → Bit :=
  fun i => qubitBitEquiv (x i)

private theorem evaluateFanoutBasis
    (B : FanoutBlock n q) (x : Fin n → Bit) :
    ∀ i : QubitBasis n, (blockFanoutGate B.sites B.pivot B.arity).gate i (wordOfBits x) =
      if i = wordOfBits (B.run x) then 1 else 0 := by
  intro i
  rw [show (blockFanoutGate B.sites B.pivot B.arity).gate =
    basisPermutation _ from rfl, basisPermutation_apply]
  congr 2
  funext j
  change qubitBitEquiv.symm ((B.run (bitsOfWord (wordOfBits x))) j) =
    qubitBitEquiv.symm (B.run x j)
  have hx : bitsOfWord (wordOfBits x) = x := by
    funext k
    exact qubitBitEquiv.apply_symm_apply (x k)
  rw [hx]

private theorem gate_mul_single
    (B : FanoutBlock n q) (x : Fin n → Bit) :
    (blockFanoutGate B.sites B.pivot B.arity).gate.mulVec
        (Pi.single (wordOfBits x) (1 : ℂ)) =
      Pi.single (wordOfBits (B.run x)) (1 : ℂ) := by
  classical
  funext i
  have h := evaluateFanoutBasis B x i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm] using h

/-- The physical parallel layer sends a computational basis vector to the
binary word after the simultaneous disjoint block updates. -/
theorem fanoutLayerOfBlocks_eval_basis (blocks : List (FanoutBlock n q))
    (hdis : blocks.Pairwise fun A B => Disjoint A.sites B.sites)
    (x : Fin n → Bit) :
    (fanoutLayerOfBlocks blocks hdis).eval.mulVec (Pi.single (wordOfBits x) (1 : ℂ)) =
      Pi.single (wordOfBits (blocks.foldl (fun y B => B.run y) x)) (1 : ℂ) := by
  classical
  induction blocks generalizing x with
  | nil =>
    change (1 : Operator (QubitBasis n)).mulVec (Pi.single (wordOfBits x) 1) = _
    rw [Matrix.one_mulVec]
    rfl
  | cons B rest ih =>
    have hrest := (List.pairwise_cons.mp hdis).2
    change (listGateEval
      ((blockFanoutGate B.sites B.pivot B.arity) ::
        rest.map (fun T => blockFanoutGate T.sites T.pivot T.arity))).mulVec
      (Pi.single (wordOfBits x) (1 : ℂ)) =
        Pi.single (wordOfBits (rest.foldl (fun y T => T.run y) (B.run x))) 1
    rw [listGateEval_cons, ← Matrix.mulVec_mulVec, gate_mul_single]
    exact ih hrest (B.run x)

#print axioms fanoutLayerOfBlocks_eval_basis

end CriticalDepth.FaultShorSaturation