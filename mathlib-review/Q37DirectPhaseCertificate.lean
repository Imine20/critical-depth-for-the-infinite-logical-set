import Q37PhaseBridge

/-!
# Direct bounded coefficient tests for the Q37 phase polynomials

The enumerator visits only subsets of size at most the polynomial degree.
The four kernel checks validate the signed coefficient polynomial at
those subsets. Low-degree reconstruction then covers every coefficient set.
-/

open scoped BigOperators

namespace CriticalDepth.Q37BinaryData

/-- List of subsets with at most r entries from the input list. -/
def smallFinsets {α : Type*} [DecidableEq α] (r : ℕ) : List α → List (Finset α)
  | [] => [∅]
  | i :: tail =>
    match r with
    | 0 => [∅]
    | k + 1 => smallFinsets (k + 1) tail ++ (smallFinsets k tail).map (insert i)
termination_by structural l => l

theorem mem_smallFinsets {α : Type*} [DecidableEq α]
    (indices : List α) (S : Finset α) (r : ℕ)
    (hS : ∀ i ∈ S, i ∈ indices) (hcard : S.card ≤ r) :
    S ∈ smallFinsets r indices := by
  induction indices generalizing S r with
  | nil =>
    have he : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      fun j hj => List.not_mem_nil (hS j hj)
    simp [smallFinsets, he]
  | cons i tail ih =>
    cases r with
    | zero =>
      have he : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      simp [smallFinsets, he]
    | succ r =>
      change S ∈ smallFinsets (r + 1) tail ++ (smallFinsets r tail).map (insert i)
      by_cases hi : i ∈ S
      · apply List.mem_append_right
        apply List.mem_map.mpr
        refine ⟨S.erase i, ih (S.erase i) r ?_ ?_, Finset.insert_erase hi⟩
        · intro j hj
          exact (List.mem_cons.mp (hS j (Finset.mem_of_mem_erase hj))).resolve_left
            (Finset.ne_of_mem_erase hj)
        · rw [Finset.card_erase_of_mem hi]
          omega
      · apply List.mem_append_left
        apply ih S (r + 1) _ hcard
        intro j hj
        exact (List.mem_cons.mp (hS j hj)).resolve_left (fun h => hi (h ▸ hj))

/-- The list-based evaluation used by the finite Lean certificate. -/
def integerPhaseDefect (rows blocks : List ℕ) (logical : ℕ) (shift : Bool)
    (S : Finset (Fin rows.length)) : ℤ :=
  (blocks.map fun b => (if shift then affineBlockSign logical b else 1) *
    supportParity (coefficientSupport rows b) S).sum

theorem integerPhaseDefect_eq_sum (rows blocks : List ℕ) (logical : ℕ)
    (shift : Bool) (S : Finset (Fin rows.length)) :
    integerPhaseDefect rows blocks logical shift S =
      ∑ b : Fin blocks.length, (if shift then affineBlockSign logical blocks[b] else 1) *
        supportParity (coefficientSupport rows blocks[b]) S := by
  unfold integerPhaseDefect
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

/-- A finite exact modular test for every selected coefficient support
of size at most r. -/
def phasePolynomialTests (rows blocks : List ℕ) (logical r : ℕ)
    (shift : Bool) : Bool :=
  (smallFinsets r (List.ofFn fun i : Fin rows.length => i)).all
    (fun S => integerPhaseDefect rows blocks logical shift S % (2 ^ r : ℤ) == 0)

theorem phase_defect_of_verified_tests (rows blocks : List ℕ) (logical r : ℕ)
    (shift : Bool) (h : phasePolynomialTests rows blocks logical r shift = true) :
    ∀ S : Finset (Fin rows.length),
      (∑ b : Fin blocks.length,
        ((if shift then affineBlockSign logical blocks[b] else 1) : ZMod (2 ^ r)) *
          (supportParity (coefficientSupport rows blocks[b]) S : ZMod (2 ^ r))) = 0 := by
  apply phase_defect_of_small_tests rows blocks logical r shift
  intro S hS
  have hm := mem_smallFinsets (List.ofFn fun i : Fin rows.length => i) S r
    (fun i _ => List.mem_ofFn.mpr ⟨i, rfl⟩) hS
  unfold phasePolynomialTests at h
  have hs := beq_iff_eq.mp (List.all_eq_true.mp h S hm)
  have hc : (integerPhaseDefect rows blocks logical shift S : ZMod (2 ^ r)) = 0 := by
    have hs' : integerPhaseDefect rows blocks logical shift S % ((2 ^ r : ℕ) : ℤ) = 0 := by
      exact_mod_cast hs
    rw [← ZMod.intCast_mod, hs', Int.cast_zero]
  rw [integerPhaseDefect_eq_sum, Int.cast_sum] at hc
  push_cast at hc
  exact hc

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem q37_parity_t_defect_tests :
    phasePolynomialTests xChecks parityBlocks logicalX 3 false = true ∧
      phasePolynomialTests xChecks parityBlocks logicalX 3 true = true := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem q37_line_x_defect_tests :
    phasePolynomialTests zChecks lineBlocks logicalZ 2 false = true ∧
      phasePolynomialTests zChecks lineBlocks logicalZ 2 true = true := by
  decide

#print axioms mem_smallFinsets
#print axioms phase_defect_of_verified_tests
#print axioms q37_parity_t_defect_tests
#print axioms q37_line_x_defect_tests

end CriticalDepth.Q37BinaryData
