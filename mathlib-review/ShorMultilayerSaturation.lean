import ShorGroupedAction
import ShorFaultWitnessAmbiguity

/-!
# The two Shor fault histories at every depth at least two
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultCircuitSupport CriticalDepth.FaultHistoryGeometry
open CriticalDepth.IndependentFaultHistories CriticalDepth.ShorFaultWitness
open scoped ENat Topology

variable {g q h c : ℕ} {seed : Cell q h}

private theorem fullX_shorColumnCycleUnion (j : Fin c) (p : Cell q h) :
    fullX (shorColumnCycleUnion (g := g) j p) =
      pauliMatrix 0 (physicalXWord (shorWordLinearEquiv (ShorRows g q h) c
        (liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) (mark {p})))) := by
  apply ShorFaultWitnessAmbiguity.fullX_eq_physicalXWord
  intro i
  rw [← mark_shorColumnCycleUnion]
  change _ ↔ mark (shorColumnCycleUnion (g := g) j p)
    ((shorSiteEquiv (ShorRows g q h) c).symm ((shorSiteEquiv (ShorRows g q h) c) i)) ≠ 0
  rw [Equiv.symm_apply_apply]
  by_cases hi : i ∈ shorColumnCycleUnion (g := g) j p <;> simp [mark, hi]

theorem exists_shorGrouped_histories (S : IndexedCellSchedule q h seed)
    (hq : 0 < q) (hh : 2 ≤ h) (hg : 0 < g) (j : Fin c) :
    let L := shorGroupedCircuit (g := g) (c := c) S
    ∃ x y : History (fun i : Location L => FaultLabel i),
      x ≠ y ∧ (faults x).card = g ∧ (faults y).card = g ∧
      (let e := shorWordLinearEquiv (ShorRows g q h) c
       let A := liftCellWord (shorCellLayout g q h c) (chooseShorColumn j)
         (mark (Finset.univ.erase S.pivot))
       let D := liftCellWord (shorCellLayout g q h c) (chooseShorColumn j) (mark {S.pivot})
       outputHistory (insertion L) physicalFault x (chronologicalFaults x) =
           pauliMatrix 0 (physicalXWord (e A)) ∧
       outputHistory (insertion L) physicalFault y (chronologicalFaults y) =
           pauliMatrix 0 (physicalXWord (e D))) := by
  classical
  let L := shorGroupedCircuit (g := g) (c := c) S
  have hlen : L.length = h := shorGroupedCircuit_length S hh
  let first : Fin L.length := ⟨0, by omega⟩
  let last : Fin L.length := ⟨L.length - 1, by omega⟩
  have hfirst : L.get first = (shorBoundaryLayer S.first seed S.first_idle).normalized := rfl
  have hlast : L.get last = (shorBoundaryLayer S.last S.pivot S.last_idle).normalized := by
    let head := (shorBoundaryLayer (g := g) (c := c) S.first seed S.first_idle).normalized
    let middle := S.middle.map fun P => parentNativeLayer (P.liftCells (shorCellLayout g q h c))
    let tail := (shorBoundaryLayer (g := g) (c := c) S.last S.pivot S.last_idle).normalized
    have hL : L = (head :: middle) ++ [tail] := rfl
    have hn : L ≠ [] := by rw [hL]; simp
    have hget : L.get last = L.getLast hn := by
      rw [List.get_eq_getElem, List.getLast_eq_getElem]
    rw [hget]
    have htail : L.getLast hn = ((head :: middle) ++ [tail]).getLast (by simp) := by
      simp only [hL]
    rw [htail, List.getLast_append_singleton]
  have htail : L.drop (first.val + 1) = shorCircuitTail S := rfl
  have hempty : L.drop (last.val + 1) = [] := by
    rw [List.drop_eq_nil_iff]
    change L.length ≤ L.length - 1 + 1
    omega
  have dis (p : Cell q h) (a b : Fin g) (hne : a ≠ b) :
      Disjoint (shorCycle a j p).sites (shorCycle b j p).sites :=
    shorCycle_sites_disjoint (g := g) (q := q) (h := h) (c := c)
      p (a := (a, j)) (b := (b, j)) (fun he => hne (congrArg Prod.fst he))
  obtain ⟨x, hfirstX, hxg, hx⟩ := exists_singleLayerXHistory_of_supports L first
    (fun i : Fin g => (shorCycle i j seed).sites) (fun i => shorCycle_nonempty i j seed hq)
    (dis seed) (fun i => by rw [hfirst]; exact shorBoundaryLayer_has_cycle_slot _ _ _ i j hq)
  obtain ⟨y, hlastY, hyg, hy⟩ := exists_singleLayerXHistory_of_supports L last
    (fun i : Fin g => (shorCycle i j S.pivot).sites) (fun i => shorCycle_nonempty i j _ hq)
    (dis S.pivot) (fun i => by rw [hlast]; exact shorBoundaryLayer_has_cycle_slot _ _ _ i j hq)
  rw [Fintype.card_fin] at hxg hyg
  have hxy : x ≠ y := by
    intro he
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (hxg.symm ▸ hg)
    have hfl : first = last := (hfirstX i hi).symm.trans (hlastY i (he ▸ hi))
    have eqv := congrArg Fin.val hfl
    change 0 = L.length - 1 at eqv
    omega
  refine ⟨x, y, hxy, hxg, hyg, ?_, ?_⟩
  · rw [htail, shorCircuitTail_eval _ hq] at hx
    change _ = propagate _ (fullX (shorColumnCycleUnion (g := g) j seed)) at hx
    rw [fullX_shorColumnCycleUnion, propagate_binaryWordOperator_physicalXWord,
      LinearEquiv.symm_apply_apply, shorTailRun_seed] at hx
    exact hx
  · rw [hempty, layerSequenceEval] at hy
    change _ = propagate (1 : Operator (QubitBasis _))
      (fullX (shorColumnCycleUnion (g := g) j S.pivot)) at hy
    simpa only [propagate, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul,
      fullX_shorColumnCycleUnion] using hy

theorem exists_multilayer_lower_saturation (d q h : ℕ)
    (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 2 ≤ h) :
    ∃ (C : Code (lowerEnvelope q d h * (q ^ h + q) * d) (fun _ => 2) (2 ^ 1) 1),
      IsStabilizer C ∧ HasActualDistance C d ∧
      perCodeExponent C q h = (lowerEnvelope q d h : ℕ∞) ∧
      ∃ e : Experiment C q h, e.layers.length = h ∧ e.logical = 1 ∧
        (circuitInfidelity C e.layers e.law =O[𝓝[>] 0] fun p => p ^ lowerEnvelope q d h) ∧
        ∃ a : ℝ, 0 < a ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
          a * p ^ lowerEnvelope q d h ≤ circuitInfidelity C e.layers e.law p := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  let g := lowerEnvelope q (c + 1) h
  change ∃ (C : Code (g * (q ^ h + q) * (c + 1)) (fun _ => 2) (2 ^ 1) 1), _
  rw [← show ShorRows g q h = g * (q ^ h + q) by
    exact congrArg (fun x => g * x) (groupSize_eq_cells q h (by omega)).symm]
  have hg : 0 < g := ceilDiv_pos (by omega) _
  let seed : Cell q h := ⟨0, by unfold cellSize; omega⟩
  obtain ⟨S⟩ := exists_indexedCellSchedule q h hq hh seed
  have hrows : ShorRows g q h = g * (q ^ h + q) :=
    congrArg (fun x => g * x) (groupSize_eq_cells q h (by omega)).symm
  have hside : c + 1 ≤ ShorRows g q h := by
    rw [hrows]
    exact (ceilDiv_le_iff _ _ _ (by omega)).mp le_rfl
  let r : Fin (ShorRows g q h) := ⟨0, by omega⟩
  let j : Fin (c + 1) := 0
  let C := physicalShorCode (columns := c) r
  let L := shorGroupedCircuit (g := g) (c := c + 1) S
  have hlen : L.length = h := shorGroupedCircuit_length S hh
  let e : Experiment C q h :=
    ⟨L, hlen.le, 1, shorGroupedCircuit_implements_one S r j (by omega), uniformLaw L⟩
  obtain ⟨x, y, hxy, hxg, hyg, hx, hy⟩ := exists_shorGrouped_histories S (by omega) hh hg j
  let E := shorCellLayout g q h (c + 1)
  let eWord := shorWordLinearEquiv (ShorRows g q h) (c + 1)
  let a := eWord (liftCellWord E (chooseShorColumn j) (mark (Finset.univ.erase S.pivot)))
  let b := eWord (liftCellWord E (chooseShorColumn j) (mark {S.pivot}))
  have hab : a + b = fullXColumn j := by
    change eWord _ + eWord _ = _
    rw [← map_add]
    exact S.column_partition j
  obtain ⟨hSat, hO, a₀, ha₀, hΩ⟩ := ShorFaultWitnessAmbiguity.physicalShorCode_saturates_of_X_mask_partition
    r hside (by omega) e x y hxy a b j hx hy hab hxg hyg
  exact ⟨C, physicalShorCode_isStabilizer r, physicalShorCode_hasActualDistance r hside,
    hSat, e, hlen, rfl, hO, a₀, ha₀, hΩ⟩

#print axioms exists_shorGrouped_histories
#print axioms exists_multilayer_lower_saturation

end CriticalDepth.FaultShorSaturation