import ShorCycleAction
import ShorGroupLayout
import ShorRowActionColumns
import ShorFaultWitnessAmbiguity

/-!
# Actual depth-one Shor saturation witness

Each depth-one group has two sites in every cell. The native layer cycles
the q sites of each tag independently in every column. The two histories
fault the two different tag families in one column.
-/

namespace CriticalDepth.ShorDepthOneWitness

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.Arithmetic CriticalDepth.FaultShorSaturation
open CriticalDepth.BinaryPermutationUnitary CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultNativeModel
open CriticalDepth.IndependentFaultHistories CriticalDepth.FaultDepthArithmetic
open CriticalDepth.ShorFaultWitness CriticalDepth.ShorFaultWitnessAmbiguity
open CriticalDepth.FaultHistoryNormalization
open Filter Asymptotics
open scoped BigOperators ENat Topology

variable {n g q : ℕ}

private def tagZero : Cell q 1 := ⟨0, by simp [cellSize]⟩
private def tagOne : Cell q 1 := ⟨1, by simp [cellSize]⟩

private theorem tag_ne : tagZero (q := q) ≠ tagOne := by
  intro h
  have h' := congrArg Fin.val h
  change (0 : ℕ) = 1 at h'
  omega

private theorem tag_cases (p : Cell q 1) : p = tagZero ∨ p = tagOne := by
  have hp := p.isLt
  change p.val < cellSize q 1 at hp
  simp [cellSize] at hp
  have hv : p.val = 0 ∨ p.val = 1 := by omega
  rcases hv with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

private def depthOneCycleBlocks (g q c : ℕ) : List (SiteCycleBlock (ShorSites g q 1 c) q) :=
  shorCycleBlocks g q 1 c tagZero ++ shorCycleBlocks g q 1 c tagOne

private theorem depthOneCycleBlocks_pairwise (g q c : ℕ) :
    (depthOneCycleBlocks g q c).Pairwise fun A B => Disjoint A.sites B.sites := by
  unfold depthOneCycleBlocks
  apply List.pairwise_append.mpr
  refine ⟨shorCycleBlocks_pairwise _, shorCycleBlocks_pairwise _, ?_⟩
  intro A hA B hB
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hA
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hB
  have ha := (mem_shorCycle_sites a.1 a.2 tagZero x).mp hxA |>.2.2
  have hb := (mem_shorCycle_sites b.1 b.2 tagOne x).mp hxB |>.2.2
  exact tag_ne (ha.symm.trans hb)

private def depthOnePaperLayer (g q c : ℕ) : PaperLayer (n := ShorSites g q 1 c) (q := q) where
  gates := (depthOneCycleBlocks g q c).map SiteCycleBlock.gate
  disjoint := List.pairwise_map.mpr (depthOneCycleBlocks_pairwise g q c)

def layer (g q c : ℕ) : Layer (ShorSites g q 1 c) (fun _ => 2) q :=
  (depthOnePaperLayer g q c).normalized

private theorem binaryCyclesOnQubits (blocks : List (SiteCycleBlock n q)) :
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

private theorem filterRetainsAll (gates : List (ListGate n (fun _ => 2) q))
    (hne : ∀ G ∈ gates, G.support.Nonempty) : filterNonemptyGates gates = gates := by
  induction gates with
  | nil => rfl
  | cons G rest ih =>
    rw [filterNonemptyGates, ite_eq_right (hne G (by simp)).ne_empty]
    exact congrArg (List.cons G) (ih (fun H hH => hne H (by simp [hH])))

private def taggedRowAction (p : Cell q 1) (a : Fin (ShorRows g q 1)) :
    Fin (ShorRows g q 1) :=
  let e := groupedRowEquiv g q 1
  let z := e a
  if z.2.2 = p then e.symm (z.1, ((finRotate q).symm z.2.1, p)) else a

private theorem taggedCycleAction {c : ℕ} (p : Cell q 1)
    (x : Fin (ShorSites g q 1 c) → Bit) (a : Fin (ShorRows g q 1)) (j : Fin c) :
    siteCyclesLinearEquiv (shorCycleBlocks g q 1 c p) x
        ((shorSiteEquiv (ShorRows g q 1) c).symm (a, j)) =
      x ((shorSiteEquiv (ShorRows g q 1) c).symm (taggedRowAction p a, j)) := by
  let e := groupedRowEquiv g q 1
  let u := shorSiteEquiv (ShorRows g q 1) c
  let E := shorCellLayout g q 1 c
  let B := shorCycle (e a).1 j p
  change siteCyclesWordEquiv _ _ _ = _
  rw [siteCyclesWordEquiv_apply]
  have hE : E (u.symm (a, j)) = ((((e a).1, (e a).2.1), j), (e a).2.2) := by
    change (shorCellLayout g q 1 c) (u.symm (a, j)) = _
    simp [shorCellLayout, e, u]
  by_cases hp : (e a).2.2 = p
  · have orderE (k : Fin q) : (B.order k).val = u.symm (e.symm ((e a).1, (k, p)), j) := by
      rw [show (B.order k).val = E.symm ((((e a).1, k), j), p) from shorCycle_apply_order _ _ _ _]
      apply E.injective
      simp [E, u, e, shorCellLayout]
    have hsite : (B.order (e a).2.1).val = u.symm (a, j) := by
      rw [orderE]
      congr 2
      apply e.injective
      rw [e.apply_symm_apply]
      exact Prod.ext rfl (Prod.ext rfl hp.symm)
    rw [← hsite, runSiteCycles_on_site _ (shorCycleBlocks_pairwise p) _ B
      (shorCycle_mem_blocks _ _ _)]
    rw [orderE]
    simp [taggedRowAction, e] at hp ⊢
    rw [ite_eq_left hp]
  · rw [runSiteCycles_off_sites]
    · simp [taggedRowAction, e] at hp ⊢
      rw [ite_eq_right hp]
    · intro C hC hm
      unfold shorCycleBlocks at hC
      obtain ⟨ij, _, rfl⟩ := List.mem_map.mp hC
      have ht := ((mem_shorCycle_sites ij.1 ij.2 p (u.symm (a, j))).mp hm).2.2
      change (E (u.symm (a, j))).2 = p at ht
      rw [hE] at ht
      exact hp ht

private theorem taggedCyclesRow {c : ℕ} (p : Cell q 1) (j : Fin c) :
    ∃ T : (Fin (ShorRows g q 1) → Bit) ≃ₗ[Bit] (Fin (ShorRows g q 1) → Bit),
      siteCyclesLinearEquiv (shorCycleBlocks g q 1 c p) =
        acrossColumnsPhysicalLinearEquiv (columns := c) T := by
  obtain ⟨T, _, hT⟩ := exists_acrossColumnsPhysicalLinearEquiv_of_action
    (siteCyclesLinearEquiv (shorCycleBlocks g q 1 c p))
    (fun z i => z (taggedRowAction p i)) j (taggedCycleAction p)
  exact ⟨T, hT⟩

private theorem physicalRows_trans {rows columns : ℕ}
    (T U : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) :
    (acrossColumnsPhysicalLinearEquiv (columns := columns) T).trans
        (acrossColumnsPhysicalLinearEquiv (columns := columns) U) =
      acrossColumnsPhysicalLinearEquiv (columns := columns) (T.trans U) := by
  apply eq_acrossColumnsPhysicalLinearEquiv
  intro x i j
  change acrossColumnsPhysicalLinearEquiv (columns := columns) U
      (acrossColumnsPhysicalLinearEquiv (columns := columns) T x) _ = _
  rw [acrossColumnsPhysicalLinearEquiv_apply]
  simp_rw [acrossColumnsPhysicalLinearEquiv_apply]
  rfl

private theorem depthOneSiteRun (g q c : ℕ) (j : Fin c) :
    ∃ T : (Fin (ShorRows g q 1) → Bit) ≃ₗ[Bit] (Fin (ShorRows g q 1) → Bit),
      T 1 = 1 ∧ siteCyclesLinearEquiv (depthOneCycleBlocks g q c) =
        acrossColumnsPhysicalLinearEquiv (columns := c) T := by
  obtain ⟨U, hU⟩ := taggedCyclesRow (g := g) (q := q) tagZero j
  obtain ⟨V, hV⟩ := taggedCyclesRow (g := g) (q := q) tagOne j
  have hc : siteCyclesLinearEquiv (depthOneCycleBlocks g q c) =
      (siteCyclesLinearEquiv (shorCycleBlocks g q 1 c tagZero)).trans
        (siteCyclesLinearEquiv (shorCycleBlocks g q 1 c tagOne)) := by
    apply LinearEquiv.ext
    intro x
    change siteCyclesWordEquiv (depthOneCycleBlocks g q c) x =
      siteCyclesWordEquiv (shorCycleBlocks g q 1 c tagOne)
        (siteCyclesWordEquiv (shorCycleBlocks g q 1 c tagZero) x)
    simp only [siteCyclesWordEquiv_apply, depthOneCycleBlocks, runSiteCycles, List.foldl_append]
  have hones (p : Cell q 1) :
      siteCyclesLinearEquiv (shorCycleBlocks g q 1 c p) 1 = 1 := by
    change siteCyclesWordEquiv (shorCycleBlocks g q 1 c p) (1 : Fin (ShorSites g q 1 c) → Bit) = 1
    rw [siteCyclesWordEquiv_apply]
    apply runSiteCycles_fixes
    intros
    rfl
  have hone (p : Cell q 1)
      (R : (Fin (ShorRows g q 1) → Bit) ≃ₗ[Bit] (Fin (ShorRows g q 1) → Bit))
      (hR : siteCyclesLinearEquiv (shorCycleBlocks g q 1 c p) =
        acrossColumnsPhysicalLinearEquiv (columns := c) R) : R 1 = 1 := by
    funext i
    have h := congrFun (hones p) ((shorSiteEquiv (ShorRows g q 1) c).symm (i, j))
    rw [hR, acrossColumnsPhysicalLinearEquiv_apply] at h
    exact h
  refine ⟨U.trans V, ?_, ?_⟩
  · change V (U 1) = 1
    rw [hone tagZero U hU, hone tagOne V hV]
  · rw [hc, hU, hV, physicalRows_trans]

private theorem layer_eval (g q c : ℕ) (hq : 0 < q) :
    (layer g q c).eval =
      binaryWordOperator (siteCyclesLinearEquiv (depthOneCycleBlocks g q c)).toEquiv := by
  have hnonempty : ∀ G ∈ (depthOnePaperLayer g q c).gates, G.support.Nonempty := by
    intro G hG
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hG
    exact ⟨(B.order ⟨0, hq⟩).val, (B.order ⟨0, hq⟩).property⟩
  unfold layer
  rw [ArbitraryLayer.normalized_eval, filterRetainsAll _ hnonempty]
  change listGateEval ((depthOneCycleBlocks g q c).map SiteCycleBlock.gate) = _
  rw [listGateEval_siteCycleBlocks, binaryCyclesOnQubits]
  rfl

private def tagMask (g q c : ℕ) (j : Fin c) (p : Cell q 1) : Mask (ShorRows g q 1) c :=
  fun ij => if ij.2 = j ∧ (groupedRowEquiv g q 1 ij.1).2.2 = p then 1 else 0

private theorem tagMask_add (g q c : ℕ) (j : Fin c) :
    tagMask g q c j tagZero + tagMask g q c j tagOne = fullXColumn j := by
  funext a
  change (if a.2 = j ∧ (groupedRowEquiv g q 1 a.1).2.2 = tagZero then (1 : Bit) else 0) +
    (if a.2 = j ∧ (groupedRowEquiv g q 1 a.1).2.2 = tagOne then 1 else 0) =
      if a.2 = j then 1 else 0
  by_cases hcol : a.2 = j
  · rcases tag_cases (groupedRowEquiv g q 1 a.1).2.2 with h | h
    · simp [hcol, h, tag_ne]
    · simp [hcol, h, Ne.symm tag_ne]
  · simp [hcol]

private theorem union_eq_tagMask (g q c : ℕ) (j : Fin c) (p : Cell q 1) :
    fullX ((Finset.univ : Finset (Fin g)).biUnion fun i => (shorCycle i j p).sites) =
      pauliMatrix 0 (physicalXWord (tagMask g q c j p)) := by
  apply fullX_eq_physicalXWord
  intro x
  rw [mem_shorColumnCycleUnion]
  change (((shorSiteEquiv (ShorRows g q 1) c) x).2 = j ∧
    (groupedRowEquiv g q 1 ((shorSiteEquiv (ShorRows g q 1) c) x).1).2.2 = p) ↔
    tagMask g q c j p (shorSiteEquiv (ShorRows g q 1) c x) ≠ 0
  unfold tagMask
  split <;> simp_all

private theorem columnCycleSupports_disjoint {α β κ : Type*}
    (f : α × β → Finset κ) (b : β)
    (h : ∀ {x y}, x ≠ y → Disjoint (f x) (f y)) :
    ∀ (x y : α), x ≠ y → Disjoint (f (x, b)) (f (y, b)) := by
  intro x y hxy
  exact h (fun he => hxy (congrArg Prod.fst he))

private theorem depthOneHistory (g q c : ℕ) (hq : 0 < q) (j : Fin c) (p : Cell q 1) :
    ∃ x : History (fun t : Location [layer g q c] => FaultLabel t),
      (faults x).card = g ∧
      outputHistory (insertion [layer g q c]) physicalFault x (chronologicalFaults x) =
        pauliMatrix 0 (physicalXWord (tagMask g q c j p)) := by
  let L := [layer g q c]
  let ell : Fin L.length := ⟨0, by simp [L]⟩
  have hslots (i : Fin g) : ∃ k : Fin (ShorSites g q 1 c),
      (L.get ell).support k = (shorCycle i j p).sites := by
    have hm : shorCycle i j p ∈ depthOneCycleBlocks g q c := by
      rcases tag_cases p with rfl | rfl
      · exact List.mem_append.mpr (Or.inl (shorCycle_mem_blocks i j _))
      · exact List.mem_append.mpr (Or.inr (shorCycle_mem_blocks i j _))
    exact normalized_support_of_gate_mem (depthOnePaperLayer g q c) (shorCycle i j p).gate
      (List.mem_map.mpr ⟨_, hm, rfl⟩) (shorCycle_nonempty i j p hq)
  have hdis : ∀ (a b : Fin g), a ≠ b →
      Disjoint (shorCycle a j p).sites (shorCycle b j p).sites :=
    columnCycleSupports_disjoint (fun t : Fin g × Fin c => (shorCycle t.1 t.2 p).sites)
      j (fun {a b} hab => shorCycle_sites_disjoint (g := g) (q := q) (h := 1) (c := c) p
        (a := a) (b := b) hab)
  obtain ⟨x, _, hc, hx⟩ := exists_singleLayerXHistory_of_supports (G := Fin g) L ell
    (fun i => (shorCycle i j p).sites) (fun i => shorCycle_nonempty i j p hq) hdis hslots
  refine ⟨x, by simpa using hc, ?_⟩
  rw [hx, union_eq_tagMask]
  simp [L, ell, layerSequenceEval, propagate]

/-- The concrete depth-one construction realizes two equal-order fault
histories and the matching optimal-recovery order. -/
theorem depthOneShor_actual_witness {columns : ℕ} (q : ℕ) (hq : 2 ≤ q)
    (hd : 2 ≤ columns + 1) :
    let g := lowerEnvelope q (columns + 1) 1
    let rows := ShorRows g q 1
    ∃ i : Fin rows,
      ∃ e : Experiment (physicalShorCode (columns := columns) i) q 1,
        e.layers = [layer g q (columns + 1)] ∧ e.logical = 1 ∧
        ∃ x y : History (fun t : Location e.layers => FaultLabel t),
          x ≠ y ∧ (faults x).card = g ∧ (faults y).card = g ∧
          perCodeExponent (physicalShorCode (columns := columns) i) q 1 = (g : ℕ∞) ∧
          (circuitInfidelity (physicalShorCode (columns := columns) i) e.layers e.law
            =O[𝓝[>] 0] fun p => p ^ g) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
            c * p ^ g ≤ circuitInfidelity (physicalShorCode (columns := columns) i) e.layers e.law p := by
  dsimp only
  let g := lowerEnvelope q (columns + 1) 1
  let rows := ShorRows g q 1
  have hrows : columns + 1 ≤ rows := by
    have hbound := (ceilDiv_le_iff (columns + 1) (q ^ 1 + q) g (by omega)).mp le_rfl
    simpa [rows, ShorRows, cellSize, Nat.mul_two] using hbound
  let i : Fin rows := ⟨0, by omega⟩
  let j : Fin (columns + 1) := ⟨0, by omega⟩
  obtain ⟨T, hT, hrun⟩ := depthOneSiteRun g q (columns + 1) j
  let L := [layer g q (columns + 1)]
  have hEval : layerSequenceEval L =
      binaryWordOperator (acrossColumnsPhysicalLinearEquiv (columns := columns + 1) T).toEquiv := by
    simp only [L, layerSequenceEval, one_mul]
    rw [layer_eval g q _ (by omega), hrun]
  let e : Experiment (physicalShorCode (columns := columns) i) q 1 :=
    ⟨L, by simp [L], 1, physicalShorCode_implements_one_of_acrossColumns i T hT _ hEval,
      uniformLaw L⟩
  obtain ⟨x, hcx, hx⟩ := depthOneHistory g q (columns + 1) (by omega) j tagZero
  obtain ⟨y, hcy, hy⟩ := depthOneHistory g q (columns + 1) (by omega) j tagOne
  have hab := tagMask_add g q (columns + 1) j
  have hxy := distinct_of_X_mask_partition i j L x y _ _ hx hy hab
  refine ⟨i, e, rfl, rfl, x, y, hxy, hcx, hcy, ?_⟩
  exact physicalShorCode_saturates_of_X_mask_partition i hrows (by omega)
    e x y hxy _ _ j hx hy hab hcx hcy

/-- The depth-one case with the exact physical size in the manuscript. -/
theorem exists_depth_one_actual_lower_saturation (d q : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q) :
    ∃ (C : Code (lowerEnvelope q d 1 * (q ^ 1 + q) * d) (fun _ => 2) (2 ^ 1) 1),
      IsStabilizer C ∧ HasActualDistance C d ∧
      perCodeExponent C q 1 = (lowerEnvelope q d 1 : ℕ∞) ∧
      ∃ e : Experiment C q 1, e.layers.length = 1 ∧ e.logical = 1 ∧
        (circuitInfidelity C e.layers e.law =O[𝓝[>] 0] fun p => p ^ lowerEnvelope q d 1) ∧
        ∃ a : ℝ, 0 < a ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
          a * p ^ lowerEnvelope q d 1 ≤ circuitInfidelity C e.layers e.law p := by
  obtain ⟨columns, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  let g := lowerEnvelope q (columns + 1) 1
  have hrows : ShorRows g q 1 = g * (q ^ 1 + q) :=
    congrArg (fun x => g * x) (groupSize_eq_cells q 1 (by decide)).symm
  have hside : columns + 1 ≤ ShorRows g q 1 := by
    rw [hrows]
    exact (ceilDiv_le_iff _ _ _ (by omega)).mp le_rfl
  change ∃ (C : Code (g * (q ^ 1 + q) * (columns + 1)) (fun _ => 2) (2 ^ 1) 1), _
  rw [← hrows]
  obtain ⟨i, e, hL, hU, x, y, hxy, hcx, hcy, hSat, hO, a, ha, hΩ⟩ :=
    depthOneShor_actual_witness (columns := columns) q hq hd
  refine ⟨physicalShorCode i, physicalShorCode_isStabilizer i,
    physicalShorCode_hasActualDistance i hside, hSat, e, ?_, hU, hO, a, ha, hΩ⟩
  rw [hL]
  rfl

#print axioms exists_depth_one_actual_lower_saturation

#print axioms depthOneShor_actual_witness

end
end CriticalDepth.ShorDepthOneWitness
