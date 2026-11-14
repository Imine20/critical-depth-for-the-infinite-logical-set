import ShorBoundaryRows

/-!
# Physical depth and suffix of the grouped Shor circuit
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

variable {n g q h c : ℕ} {seed : Cell q h}

theorem filterNonemptyGates_eq_of_all_nonempty {n q : ℕ}
    (gates : List (ListGate n (fun _ => 2) q))
    (hne : ∀ G ∈ gates, G.support.Nonempty) :
    filterNonemptyGates gates = gates := by
  induction gates with
  | nil => rfl
  | cons G rest ih =>
    rw [filterNonemptyGates, if_neg (hne G (by simp)).ne_empty]
    exact congrArg (List.cons G) (ih (fun H hH => hne H (by simp [hH])))

theorem nativeParentLayer_all_nonempty {n q : ℕ}
    (p : Fin n → Option (Fin n)) (hu : ∀ i a, p i = some a → p a = none)
    (hc : ∀ a, (parentSites p a).card ≤ q) :
    ∀ G ∈ (nativeParentLayer p hu hc).gates, G.support.Nonempty := by
  intro G hG
  change G ∈ (parentBlocks p hc).map (fun B => blockFanoutGate B.sites B.pivot B.arity) at hG
  obtain ⟨B, _, rfl⟩ := List.mem_map.mp hG
  exact ⟨B.pivot.val, B.pivot.property⟩

theorem nativeParentLayer_normalized_eval {n q : ℕ}
    (P : CellParent n q) :
    (nativeParentLayer P.parent P.untouched P.arity).normalized.eval =
      binaryWordOperator P.run.toEquiv := by
  rw [ArbitraryLayer.normalized_eval, filterNonemptyGates_eq_of_all_nonempty _
    (nativeParentLayer_all_nonempty P.parent P.untouched P.arity)]
  exact nativeParentLayer_eval P.parent P.untouched P.arity

theorem siteCyclesWordEquiv_qubit (blocks : List (SiteCycleBlock n q)) :
    siteCyclesWordEquiv (α := Fin 2) blocks =
      binaryWordPermutation (siteCyclesLinearEquiv blocks).toEquiv := by
  apply Equiv.ext
  intro x
  funext i
  change siteCyclesWordEquiv blocks x i =
    qubitBitEquiv.symm (siteCyclesWordEquiv blocks (fun j => qubitBitEquiv (x j)) i)
  have commute (v : Fin n → Fin 2) :
      (fun j => qubitBitEquiv (siteCyclesWordEquiv blocks v j)) =
        siteCyclesWordEquiv blocks (fun j => qubitBitEquiv (v j)) := by
    induction blocks generalizing v with
    | nil => rfl
    | cons B rest ih =>
      change (fun j => qubitBitEquiv (siteCyclesWordEquiv rest (B.run v) j)) =
        siteCyclesWordEquiv rest (B.run (fun j => qubitBitEquiv (v j)))
      exact ih (B.run v)
  rw [← congrFun (commute x) i, qubitBitEquiv.symm_apply_apply]

theorem shorBoundaryLayer_normalized_eval (P : CellParent (cellSize q h) q)
    (p : Cell q h) (hidle : P.Idle p) (hq : 0 < q) :
    (shorBoundaryLayer (g := g) (c := c) P p hidle).normalized.eval =
      binaryWordOperator (shorBoundaryRun (g := g) (c := c) P p).toEquiv := by
  let e := shorCellLayout g q h c
  let f := P.liftCells e
  have hevery : ∀ G ∈ (shorBoundaryLayer (g := g) (c := c) P p hidle).gates,
      G.support.Nonempty := by
    intro G hG
    change G ∈ (shorCycleBlocks g q h c p).map SiteCycleBlock.gate ++
        (nativeParentLayer f.parent f.untouched f.arity).gates at hG
    rcases List.mem_append.mp hG with hG | hG
    · obtain ⟨B, _, rfl⟩ := List.mem_map.mp hG
      exact ⟨(B.order ⟨0, hq⟩).val, (B.order ⟨0, hq⟩).property⟩
    · exact nativeParentLayer_all_nonempty _ _ _ _ hG
  rw [ArbitraryLayer.normalized_eval, filterNonemptyGates_eq_of_all_nonempty _ hevery]
  change (shorBoundaryLayer (g := g) (c := c) P p hidle).eval = _
  unfold shorBoundaryLayer
  rw [cycleAndParentLayer_eval, nativeParentLayer_eval, listGateEval_siteCycleBlocks,
    siteCyclesWordEquiv_qubit, shorBoundaryRun, binaryWordOperator_trans]
  rfl

noncomputable def parentNativeLayer {n q : ℕ} (P : CellParent n q) :
    Layer n (fun _ => 2) q :=
  (nativeParentLayer P.parent P.untouched P.arity).normalized

noncomputable def shorCircuitTail (S : IndexedCellSchedule q h seed) :
    List (Layer (ShorSites g q h c) (fun _ => 2) q) :=
  (S.middle.map fun P => parentNativeLayer (P.liftCells (shorCellLayout g q h c))) ++
    [(shorBoundaryLayer S.last S.pivot S.last_idle).normalized]

noncomputable def shorGroupedCircuit (S : IndexedCellSchedule q h seed) :
    List (Layer (ShorSites g q h c) (fun _ => 2) q) :=
  (shorBoundaryLayer S.first seed S.first_idle).normalized :: shorCircuitTail S

theorem shorGroupedCircuit_length (S : IndexedCellSchedule q h seed) (hh : 2 ≤ h) :
    (shorGroupedCircuit (g := g) (c := c) S).length = h := by
  simp [shorGroupedCircuit, shorCircuitTail, S.middle_length]
  omega

def parentSequenceRun {n q : ℕ} :
    List (CellParent n q) → (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit)
  | [] => LinearEquiv.refl _ _
  | P :: ps => P.run.trans (parentSequenceRun ps)

theorem parentSequenceRun_apply {n q : ℕ} (ps : List (CellParent n q)) (x : Fin n → Bit) :
    parentSequenceRun ps x = runParents ps x := by
  induction ps generalizing x with
  | nil => rfl
  | cons P ps ih => exact ih (P.run x)

theorem parentNativeSequence_eval {n q : ℕ} (ps : List (CellParent n q)) :
    layerSequenceEval (ps.map parentNativeLayer) =
      binaryWordOperator (parentSequenceRun ps).toEquiv := by
  induction ps with
  | nil => exact binaryWordOperator_refl.symm
  | cons P ps ih =>
    rw [List.map_cons, layerSequenceEval, ih]
    change _ * (nativeParentLayer P.parent P.untouched P.arity).normalized.eval = _
    rw [nativeParentLayer_normalized_eval, parentSequenceRun, binaryWordOperator_trans]

noncomputable def shorTailRun (S : IndexedCellSchedule q h seed) :
    (Fin (ShorSites g q h c) → Bit) ≃ₗ[Bit] (Fin (ShorSites g q h c) → Bit) :=
  (parentSequenceRun (S.middle.map fun P => P.liftCells (shorCellLayout g q h c))).trans
    (shorBoundaryRun S.last S.pivot)

noncomputable def shorGroupedRun (S : IndexedCellSchedule q h seed) :
    (Fin (ShorSites g q h c) → Bit) ≃ₗ[Bit] (Fin (ShorSites g q h c) → Bit) :=
  (shorBoundaryRun S.first seed).trans (shorTailRun S)

theorem shorCircuitTail_eval (S : IndexedCellSchedule q h seed) (hq : 0 < q) :
    layerSequenceEval (shorCircuitTail (g := g) (c := c) S) =
      binaryWordOperator (shorTailRun (g := g) (c := c) S).toEquiv := by
  unfold shorCircuitTail shorTailRun
  rw [layerSequenceEval_append]
  change (1 * (shorBoundaryLayer (g := g) (c := c) S.last S.pivot S.last_idle).normalized.eval) *
    layerSequenceEval _ = _
  rw [one_mul, shorBoundaryLayer_normalized_eval _ _ _ hq, binaryWordOperator_trans,
    ← parentNativeSequence_eval, List.map_map]
  rfl

theorem shorGroupedCircuit_eval (S : IndexedCellSchedule q h seed) (hq : 0 < q) :
    layerSequenceEval (shorGroupedCircuit (g := g) (c := c) S) =
      binaryWordOperator (shorGroupedRun (g := g) (c := c) S).toEquiv := by
  unfold shorGroupedCircuit shorGroupedRun
  rw [layerSequenceEval, shorCircuitTail_eval _ hq, shorBoundaryLayer_normalized_eval _ _ _ hq,
    binaryWordOperator_trans]

#print axioms shorGroupedCircuit_length
#print axioms shorGroupedCircuit_eval

end CriticalDepth.FaultShorSaturation