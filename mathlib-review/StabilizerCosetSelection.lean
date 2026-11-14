import CriticalDepthMathlib
import Mathlib.Data.Set.Finite.Lemmas

/-!
# A minimum-weight representative of a physical stabilizer coset
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2

noncomputable section

variable {n K g : ℕ}

/-- Include the four phases, as stabilizer multiplication need not preserve
the unphased tensor representative. -/
abbrev PauliLabel (n : ℕ) := Fin 4 × (Fin n → SinglePauli)

def stabilizerCosetLabels (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (p : PauliLabel n) : Set (PauliLabel n) :=
  {q | ∃ U ∈ S, pauliMatrix q.1 q.2 =
    pauliMatrix p.1 p.2 * (U : Operator (QubitBasis n))}

theorem stabilizerCosetLabels_nonempty
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (p : PauliLabel n) : (stabilizerCosetLabels S p).Nonempty := by
  refine ⟨p, 1, S.one_mem, ?_⟩
  change pauliMatrix p.1 p.2 = pauliMatrix p.1 p.2 * 1
  rw [Matrix.mul_one]

/-- Exhaustive choice minimizes the physical weight among the finite
phase-labelled Pauli representatives in the right stabilizer coset. -/
theorem exists_min_weight_stabilizer_coset_label
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ)) (p : PauliLabel n) :
    ∃ q ∈ stabilizerCosetLabels S p,
      ∀ r ∈ stabilizerCosetLabels S p, (pauliSupport q.2).card ≤ (pauliSupport r.2).card := by
  exact Set.exists_min_image (stabilizerCosetLabels S p)
    (fun q => (pauliSupport q.2).card) (Set.toFinite _)
    (stabilizerCosetLabels_nonempty S p)

/-- All chosen representatives have exactly the same encoded action. -/
theorem stabilizerCosetLabel_encoding (C : Code n (fun _ => 2) K g)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    {p q : PauliLabel n} (h : q ∈ stabilizerCosetLabels S p) :
    pauliMatrix q.1 q.2 * C.encoding = pauliMatrix p.1 p.2 * C.encoding := by
  obtain ⟨U, hUS, hq⟩ := h
  rw [hq, Matrix.mul_assoc, encoding_fixed_of_fixedSpace C S hspace U hUS]

#print axioms exists_min_weight_stabilizer_coset_label
#print axioms stabilizerCosetLabel_encoding

end

end CriticalDepth.Manuscript20261114
