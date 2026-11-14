import ShorRowAction

/-!
# Native disjoint parity-phase layers

A block applies a scalar phase when its computational parity is odd.
For disjoint blocks these are simultaneous native gates. Their diagonal
entries depend only on the number of odd blocks.
-/

open scoped BigOperators

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation Matrix

variable {n q : ℕ}

/-- Binary parity of a computational word over the selected sites. -/
def blockOdd (S : Finset (Fin n)) (x : QubitBasis n) : Bool :=
  decide ((∑ i ∈ S, (binaryWordEquiv n x) i) = (1 : Bit))

private noncomputable def phaseEntry (z : Circle) (odd : Bool) : ℂ :=
  if odd then z else 1

private theorem phaseEntry_unit (z : Circle) (odd : Bool) :
    star (phaseEntry z odd) * phaseEntry z odd = 1 := by
  cases odd
  · simp [phaseEntry]
  · exact CriticalDepth.ReviewV2.circle_star_mul_self z

/-- A supported phase controlled by the parity of a block. -/
noncomputable def parityPhaseGate (z : Circle) (S : Finset (Fin n))
    (hS : S.card ≤ q) : ListGate n (fun _ => 2) q where
  support := S
  gate := Matrix.diagonal (fun x => phaseEntry z (blockOdd S x))
  arity := hS
  locality := by
    classical
    let localOdd (x : LocalBasis (fun _ : Fin n => 2) S) : Bool :=
      decide ((∑ i : S, qubitBitEquiv (x i)) = (1 : Bit))
    let A := Matrix.diagonal (fun x : LocalBasis (fun _ : Fin n => 2) S =>
      phaseEntry z (localOdd x))
    refine ⟨A, ?_⟩
    ext x y
    change Matrix.diagonal (fun x => phaseEntry z (blockOdd S x)) x y = localEmbed S A x y
    have hr (x : QubitBasis n) : blockOdd S x = localOdd (fun i : S => x i.val) := by
      have hsum : (∑ i : S, qubitBitEquiv (x i.val)) =
          ∑ i ∈ S, (binaryWordEquiv n x) i :=
        Finset.sum_coe_sort S (fun i => qubitBitEquiv (x i))
      unfold blockOdd localOdd
      rw [hsum]
    by_cases hxy : x = y
    · subst y
      have hout : ∀ i, i ∉ S → x i = x i := fun _ _ => rfl
      rw [Matrix.diagonal_apply_eq, hr]
      unfold localEmbed
      split
      · exact (Matrix.diagonal_apply_eq (fun a : LocalBasis (fun _ : Fin n => 2) S => phaseEntry z (localOdd a)) (fun i => x i.val)).symm
      · rename_i hn
        exact (hn hout).elim
    · rw [Matrix.diagonal_apply_ne _ hxy]
      unfold localEmbed
      split
      · rename_i hout
        have hlocal : (fun i : S => x i.val) ≠ (fun i : S => y i.val) := by
          intro h
          apply hxy
          funext i
          by_cases hi : i ∈ S
          · exact congrFun h ⟨i, hi⟩
          · exact hout i hi
        exact (Matrix.diagonal_apply_ne _ hlocal).symm
      · rfl
  unitary := by
    classical
    have hs :
        star (Matrix.diagonal (fun x => phaseEntry z (blockOdd S x)) : Operator (QubitBasis n)) =
          Matrix.diagonal (fun x => star (phaseEntry z (blockOdd S x))) := by
      ext x y
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      by_cases h : x = y
      · subst y
        simp
      · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), star_zero]
    constructor
    · rw [hs, Matrix.diagonal_mul_diagonal]
      simp only [phaseEntry_unit, Matrix.diagonal_one]
    · rw [hs, Matrix.diagonal_mul_diagonal]
      simp only [mul_comm (phaseEntry _ _), phaseEntry_unit, Matrix.diagonal_one]

/-- A genuine native layer on a supplied pairwise disjoint block family. -/
noncomputable def parityPhaseLayer (z : Circle)
    (blocks : List {S : Finset (Fin n) // S.card ≤ q})
    (hdis : blocks.Pairwise fun A B => Disjoint A.val B.val) :
    ArbitraryLayer n (fun _ => 2) q where
  gates := blocks.map fun S => parityPhaseGate z S.val S.property
  disjoint := by
    rw [List.pairwise_map]
    exact hdis

/-- The number of parity blocks with an odd number of one bits. -/
def countOddBlocks
    (blocks : List {S : Finset (Fin n) // S.card ≤ q}) (x : QubitBasis n) : ℕ :=
  (blocks.filter fun S => blockOdd S.val x).length

private theorem eval_parityPhase_list (z : Circle)
    (blocks : List {S : Finset (Fin n) // S.card ≤ q}) :
    listGateEval (blocks.map fun S => parityPhaseGate z S.val S.property) =
      Matrix.diagonal (fun x => (z : ℂ) ^ countOddBlocks blocks x) := by
  classical
  induction blocks with
  | nil =>
    simp [countOddBlocks]
  | cons S rest ih =>
    simp only [List.map_cons, listGateEval_cons, ih]
    change Matrix.diagonal (fun x => (z : ℂ) ^ countOddBlocks rest x) *
      Matrix.diagonal (fun x => phaseEntry z (blockOdd S.val x)) = _
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext x
    cases h : blockOdd S.val x
    · simp [countOddBlocks, h, phaseEntry]
    · simp [countOddBlocks, h, phaseEntry, pow_add, mul_comm]

theorem parityPhaseLayer_eval (z : Circle)
    (blocks : List {S : Finset (Fin n) // S.card ≤ q})
    (hdis : blocks.Pairwise fun A B => Disjoint A.val B.val) :
    (parityPhaseLayer z blocks hdis).eval =
      Matrix.diagonal (fun x => (z : ℂ) ^ countOddBlocks blocks x) :=
  eval_parityPhase_list z blocks

private theorem parityPhase_filterNonemptyGates (z : Circle)
    (blocks : List {S : Finset (Fin n) // S.card ≤ q})
    (hne : ∀ S ∈ blocks, S.val.Nonempty) :
    filterNonemptyGates (blocks.map fun S => parityPhaseGate z S.val S.property) =
      blocks.map fun S => parityPhaseGate z S.val S.property := by
  induction blocks with
  | nil => rfl
  | cons S blocks ih =>
    have hs : (parityPhaseGate z S.val S.property).support ≠ ∅ :=
      (hne S (List.mem_cons_self ..)).ne_empty
    rw [List.map_cons, filterNonemptyGates, ite_eq_right hs,
      ih (fun T hT => hne T (List.mem_cons_of_mem S hT))]

/-- Normalization embeds the nonempty parity blocks into the padded
native layer with exactly the same total diagonal. -/
theorem parityPhaseLayer_normalized_eval (z : Circle)
    (blocks : List {S : Finset (Fin n) // S.card ≤ q})
    (hdis : blocks.Pairwise fun A B => Disjoint A.val B.val)
    (hne : ∀ S ∈ blocks, S.val.Nonempty) :
    (parityPhaseLayer z blocks hdis).normalized.eval =
      Matrix.diagonal (fun x => (z : ℂ) ^ countOddBlocks blocks x) := by
  rw [ArbitraryLayer.normalized_eval]
  change listGateEval (filterNonemptyGates (blocks.map fun S => parityPhaseGate z S.val S.property)) = _
  rw [parityPhase_filterNonemptyGates z blocks hne]
  exact eval_parityPhase_list z blocks

/-- An exponent modulo the order of a phase gives the same amplitude. -/
theorem phase_pow_modEq (z : ℂ) {m a b : ℕ}
    (hz : z ^ m = 1) (hab : a % m = b % m) : z ^ a = z ^ b := by
  have hmod (t : ℕ) : z ^ t = z ^ (t % m) := by
    conv_lhs => rw [← Nat.mod_add_div t m]
    rw [pow_add, pow_mul, hz, one_pow, mul_one]
  rw [hmod a, hmod b, hab]

/-- A diagonal gate implements the indicated logical diagonal if its phase
matches the encoded-basis phase at all nonzero encoding entries. -/
theorem diagonal_mul_encoding_of_nonzero {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (V : Matrix (QubitBasis n) κ ℂ) (p : QubitBasis n → ℂ) (d : κ → ℂ)
    (h : ∀ x b, V x b ≠ 0 → p x = d b) :
    Matrix.diagonal p * V = V * Matrix.diagonal d := by
  ext x b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hb : V x b = 0
  · rw [hb, mul_zero, zero_mul]
  · rw [h x b hb, mul_comm]

#print axioms parityPhaseGate
#print axioms parityPhaseLayer_eval
#print axioms parityPhaseLayer_normalized_eval
#print axioms phase_pow_modEq
#print axioms diagonal_mul_encoding_of_nonzero

end CriticalDepth.Q37BinaryData
