import Q37DirectPhaseCertificate
import Q37PhaseCoefficientWords
import Q37PhysicalParityLayers

/-!
# The Q37 parity layer phases on the two binary cosets
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCode

/-- Number of odd block parities evaluated directly on a binary word. -/
def oddWordCount (blocks : List ℕ) (w : Q37Word) : ℕ :=
  (blocks.filter fun b => decide (dotProduct (wordOfNatMask 37 b) w = 1)).length

private theorem filtered_len_eq_int_sum {α : Type*} (L : List α) (p : α → Prop)
    [DecidablePred p] : ((L.filter fun b => decide (p b)).length : ℤ) =
      (L.map fun b => if p b then (1 : ℤ) else 0).sum := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    by_cases h : p b
    · simp only [List.filter_cons, decide_eq_true_eq.mpr h, ite_true, List.length_cons,
        List.map_cons, List.sum_cons, ite_eq_left h]
      push_cast
      simpa [add_comm] using congrArg (fun z : ℤ => 1 + z) ih
    · simpa [List.filter_cons, h] using ih

private theorem list_map_sum_sub {α : Type*} (L : List α) (f g : α → ℤ) :
    (L.map f).sum - (L.map g).sum = (L.map fun b => f b - g b).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    abel

private theorem oddWordCount_mod_eq_phaseDefect (rows blocks : List ℕ)
    (logical r : ℕ) (shift : Bool) (S : Finset (Fin rows.length)) :
    (oddWordCount blocks
        ((coefficientWord rows.length S ᵥ* checkMatrix rows) +
          if shift then wordOfNatMask 37 logical else 0) : ZMod (2 ^ r)) -
      (oddWordCount blocks (if shift then wordOfNatMask 37 logical else 0) : ZMod (2 ^ r)) =
      (integerPhaseDefect rows blocks logical shift S : ZMod (2 ^ r)) := by
  classical
  let v : Q37Word := coefficientWord rows.length S ᵥ* checkMatrix rows
  let w : Q37Word := if shift then wordOfNatMask 37 logical else 0
  have hTerm (b : ℕ) :
      (if dotProduct (wordOfNatMask 37 b) (v + w) = 1 then (1 : ℤ) else 0) -
        (if dotProduct (wordOfNatMask 37 b) w = 1 then 1 else 0) =
        (if shift then affineBlockSign logical b else 1) *
          supportParity (coefficientSupport rows b) S := by
    have hv : dotProduct (wordOfNatMask 37 b) v =
        (supportParity (coefficientSupport rows b) S : CSSBit) :=
      coefficient_eval_eq_supportParity rows b S
    rw [dotProduct_add, hv]
    cases shift
    · have hw : dotProduct (wordOfNatMask 37 b) w = 0 := by
        simp [w]
      rw [hw]
      unfold supportParity
      split <;> norm_num
    · have hw : dotProduct (wordOfNatMask 37 b) w = (dot b logical : CSSBit) := by
        simp only [w, Bool.true_eq, ite_true, dotProduct_wordOfNatMask]
      rw [hw]
      unfold supportParity affineBlockSign
      have hb : dot b logical < 2 := by
        unfold dot
        exact Nat.mod_lt _ (by decide)
      generalize dot b logical = s at hb ⊢
      interval_cases s <;> split <;> decide
  let f (b : ℕ) : ℤ := if dotProduct (wordOfNatMask 37 b) (v + w) = 1 then 1 else 0
  let g (b : ℕ) : ℤ := if dotProduct (wordOfNatMask 37 b) w = 1 then 1 else 0
  let u (b : ℕ) : ℤ := (if shift then affineBlockSign logical b else 1) *
    supportParity (coefficientSupport rows b) S
  have hF : (oddWordCount blocks (v + w) : ℤ) = (blocks.map f).sum :=
    filtered_len_eq_int_sum blocks (fun b => dotProduct (wordOfNatMask 37 b) (v + w) = 1)
  have hG : (oddWordCount blocks w : ℤ) = (blocks.map g).sum :=
    filtered_len_eq_int_sum blocks (fun b => dotProduct (wordOfNatMask 37 b) w = 1)
  have hMap : blocks.map (fun b => f b - g b) = blocks.map u :=
    List.map_congr_left (fun b _ => hTerm b)
  have hInt :
      (oddWordCount blocks (v + w) : ℤ) - (oddWordCount blocks w : ℤ) =
        integerPhaseDefect rows blocks logical shift S :=
    (congrArg₂ (· - ·) hF hG).trans ((list_map_sum_sub blocks f g).trans (congrArg List.sum hMap))
  have he := congrArg (fun z : ℤ => (z : ZMod (2 ^ r))) hInt
  change (oddWordCount blocks (v + w) : ZMod (2 ^ r)) - (oddWordCount blocks w : ZMod (2 ^ r)) = _
  simpa only [Int.cast_sub, Int.cast_natCast] using he

/-- The registered finite tests certify the phase at every word in either
logical coset parameterized by a row coefficient vector. -/
theorem oddWordCount_mod_of_verified_tests
    (rows blocks : List ℕ) (logical r : ℕ) (shift : Bool)
    (hTest : phasePolynomialTests rows blocks logical r shift = true)
    (v : Fin rows.length → CSSBit) :
    oddWordCount blocks (v ᵥ* checkMatrix rows +
        if shift then wordOfNatMask 37 logical else 0) % (2 ^ r) =
      oddWordCount blocks (if shift then wordOfNatMask 37 logical else 0) % (2 ^ r) := by
  obtain ⟨S, rfl⟩ := exists_coefficientWord rows.length v
  have he := oddWordCount_mod_eq_phaseDefect rows blocks logical r shift S
  have hz : (integerPhaseDefect rows blocks logical shift S : ZMod (2 ^ r)) = 0 := by
    rw [integerPhaseDefect_eq_sum, Int.cast_sum]
    push_cast
    exact phase_defect_of_verified_tests rows blocks logical r shift hTest S
  rw [hz] at he
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (sub_eq_zero.mp he)

/-- For the parity blocks, logical zero has phase exponent zero modulo eight;
logical one has exponent seven. -/
theorem q37_parity_phase_on_span (shift : Bool) (v : Fin xChecks.length → CSSBit) :
    oddWordCount parityBlocks
      (v ᵥ* checkMatrix xChecks + if shift then q37LogicalX else 0) % 8 =
        if shift then 7 else 0 := by
  have hTest : phasePolynomialTests xChecks parityBlocks logicalX 3 shift = true := by
    cases shift
    · exact q37_parity_t_defect_tests.1
    · exact q37_parity_t_defect_tests.2
  have he := oddWordCount_mod_of_verified_tests xChecks parityBlocks logicalX 3 shift hTest v
  refine he.trans ?_
  cases shift <;> decide

/-- For the line blocks in the Fourier basis the two exponents are zero
and three modulo four. -/
theorem q37_line_phase_on_span (shift : Bool) (v : Fin zChecks.length → CSSBit) :
    oddWordCount lineBlocks
      (v ᵥ* checkMatrix zChecks + if shift then q37LogicalZ else 0) % 4 =
        if shift then 3 else 0 := by
  have hTest : phasePolynomialTests zChecks lineBlocks logicalZ 2 shift = true := by
    cases shift
    · exact q37_line_x_defect_tests.1
    · exact q37_line_x_defect_tests.2
  have he := oddWordCount_mod_of_verified_tests zChecks lineBlocks logicalZ 2 shift hTest v
  refine he.trans ?_
  cases shift <;> decide

#print axioms q37_parity_phase_on_span
#print axioms q37_line_phase_on_span

end CriticalDepth.Q37BinaryData
