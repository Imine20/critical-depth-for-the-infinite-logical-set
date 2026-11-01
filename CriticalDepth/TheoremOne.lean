import CriticalDepth.InsertionDetection
import CriticalDepth.AlgebraicRigidity
import CriticalDepth.AlgebraicFiniteImage
import CriticalDepth.CircuitPoints
import CriticalDepth.ProjectiveFaithfulness
import CriticalDepth.ProjectiveTopology
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Finiteness for the declared bounded-depth circuit model

The proof derives the algebraic derivative identities from actual tensor
support, distance detection, inverse pairs, and the encoded action. It then
uses the Noetherian coordinate algebra and the faithful projective-coordinate
map. Only the finite support arrangements are enumerated; circuit matrices
themselves remain arbitrary.

The final proposition is the existing `Manuscript.theoremOne`, whose layers
have `Fin n` slots. The separate normalization from arbitrary finite gate
lists to this declared circuit model is not supplied by this module.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

private theorem theoremOne_pow_mono (q a b : ℕ) (hq : 1 ≤ q) (hab : a ≤ b) :
    q ^ a ≤ q ^ b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hk : 1 ≤ q ^ k := by
    have hpos : 0 < q ^ k := pow_pos (by omega : 0 < q) k
    omega
  simpa only [mul_one] using Nat.mul_le_mul_left (q ^ a) hk

private theorem theoremOne_split_short (q d h before after : ℕ)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (hcounts : before + 1 + after = h) :
    q ^ (after + 1) < d ∨ q ^ (before + 1) < d := by
  by_cases hb : before + 1 ≤ Arithmetic.ceilHalf h
  · exact Or.inr ((theoremOne_pow_mono q _ _ hq hb).trans_lt hcone)
  · have ha : after + 1 ≤ Arithmetic.ceilHalf h := by
      unfold Arithmetic.ceilHalf at *
      omega
    exact Or.inl ((theoremOne_pow_mono q _ _ hq ha).trans_lt hcone)

variable {n ℓ g d q h : ℕ} {dim : Fin n → ℕ}

/-- The derivative premise of the algebraic finite-image theorem is proved
from the actual code, distance, layout, and numerical cone bound. -/
theorem circuitPoint_projective_derivation_zero
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (L : Fin h → Layer n dim q)
    {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (D : Derivation ℂ 𝕂 𝕂) :
    ∀ a b c e : Fin ℓ,
      D (solutionLogical C (layoutSupport L) ψ false a b *
        solutionLogical C (layoutSupport L) ψ true c e) = 0 := by
  letI : Nonempty (Fin g) := ⟨⟨0, by omega⟩⟩
  let layers := List.ofFn (solutionFieldLayer C L ψ)
  let W := solutionLogical C (layoutSupport L) ψ false
  let Wi := solutionLogical C (layoutSupport L) ψ true
  let Z := solutionGauge C (layoutSupport L) ψ false
  let Zi := solutionGauge C (layoutSupport L) ψ true
  let E := C.encoding.conjTranspose.map (algebraMap ℂ 𝕂)
  let V := C.encoding.map (algebraMap ℂ 𝕂)
  have hW : W * Wi = 1 ∧ Wi * W = 1 := solutionLogical_inverse C (layoutSupport L) ψ
  have hZ : Z * Zi = 1 ∧ Zi * Z = 1 := solutionGauge_inverse C (layoutSupport L) ψ
  have hencoded : fieldLayerSequenceEval layers * V = V * (W ⊗ₖ Z) := by
    simpa only [layers, V, W, Z, solutionTotal_eq_fieldLayerSequence] using
      solution_encoding C (layoutSupport L) ψ
  have hdual : E * fieldLayerSequenceEval layers = (W ⊗ₖ Z) * E := by
    simpa only [layers, E, W, Z, solutionTotal_eq_fieldLayerSequence] using
      solution_encoding_dual C (layoutSupport L) ψ
  have hshort : ∀ before M after, layers = before ++ M :: after →
      q ^ (after.length + 1) < d ∨ q ^ (before.length + 1) < d := by
    intro before M after heq
    have hlen := congrArg List.length heq
    simp only [layers, List.length_ofFn, List.length_append, List.length_cons] at hlen
    apply theoremOne_split_short q d h before.length after.length hq hcone
    omega
  have hcompression := fieldLayerSequence_derivative_mem_gaugeOnly
    C hDetect hq D layers W Wi Z Zi hW hZ hencoded hdual hshort
  obtain ⟨M, hM⟩ := hcompression
  have hEV : E * V = 1 := solution_encoding_isometry (𝕂 := 𝕂) C
  have hE : matrixDerivation D E = 0 := matrixDerivation_constant D _
  have hV : matrixDerivation D V = 0 := matrixDerivation_constant D _
  have hU := fieldLayerSequence_mutual_inverse layers
  exact encoded_projective_coordinates_derivation_zero D E V
    (fieldLayerSequenceEval layers) (fieldLayerSequenceInv layers) W Wi Z Zi M
    hEV hE hV hU.1 hU.2 hW.1 hW.2 hZ.1 hZ.2 hencoded hdual hM

abbrev LogicalCoordinateIndex (ℓ : ℕ) := (Fin ℓ × Fin ℓ) × (Fin ℓ × Fin ℓ)

/-- These are precisely the entries of conjugation when the inverse
logical coordinates are evaluated at the adjoint. -/
def circuitLogicalCoordinate (C : Code n dim ℓ g)
    (support : GateIndex n h → Finset (Fin n)) (i : LogicalCoordinateIndex ℓ) :
    CircuitCoordinateRing (C := C) (support := support) :=
  Ideal.Quotient.mk (circuitIdeal support C)
    (logicalPolynomial support false i.1.1 i.2.1 *
      logicalPolynomial support true i.2.2 i.1.2)

def circuitConjugationCoordinates (C : Code n dim ℓ g)
    (support : GateIndex n h → Finset (Fin n))
    {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
    (ψ : CircuitCoordinateRing (C := C) (support := support) →ₐ[ℂ] 𝕂) :
    Matrix (Fin ℓ × Fin ℓ) (Fin ℓ × Fin ℓ) 𝕂 :=
  fun p r => ψ (circuitLogicalCoordinate C support (p, r))

theorem circuitConjugationCoordinates_apply (C : Code n dim ℓ g)
    (support : GateIndex n h → Finset (Fin n))
    {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
    (ψ : CircuitCoordinateRing (C := C) (support := support) →ₐ[ℂ] 𝕂)
    (p r : Fin ℓ × Fin ℓ) :
    circuitConjugationCoordinates C support ψ p r =
      solutionLogical C support ψ false p.1 r.1 *
        solutionLogical C support ψ true r.2 p.2 := by
  change circuitPointMap C support ψ
      (logicalPolynomial support false p.1 r.1 * logicalPolynomial support true r.2 p.2) = _
  rw [map_mul]
  rfl

theorem circuitConjugationCoordinates_range_finite
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (L : Fin h → Layer n dim q) :
    (Set.range (circuitConjugationCoordinates (𝕂 := ℂ) C (layoutSupport L))).Finite := by
  let R := CircuitCoordinateRing (C := C) (support := layoutSupport L)
  let coords : LogicalCoordinateIndex ℓ → R := circuitLogicalCoordinate C (layoutSupport L)
  have hflat : (Set.range fun ψ : R →ₐ[ℂ] ℂ => fun i => ψ (coords i)).Finite := by
    apply evaluation_image_finite_of_all_field_derivations ℂ R coords
    intro 𝕂 _ _ ψ i D
    rcases i with ⟨⟨a, e⟩, ⟨b, c⟩⟩
    change D (circuitPointMap C (layoutSupport L) ψ
      (logicalPolynomial (layoutSupport L) false a b *
        logicalPolynomial (layoutSupport L) true c e)) = 0
    rw [map_mul]
    exact circuitPoint_projective_derivation_zero C hDetect hg hq hcone L ψ D a b c e
  let unflatten : (LogicalCoordinateIndex ℓ → ℂ) → Operator (Fin ℓ × Fin ℓ) :=
    fun f p r => f (p, r)
  apply (hflat.image unflatten).subset
  rintro A ⟨ψ, rfl⟩
  exact ⟨(fun i => ψ (coords i)), ⟨ψ, rfl⟩, rfl⟩

theorem circuitConjugationCoordinates_actualCircuitPoint
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    circuitConjugationCoordinates C (layoutSupport L)
      (actualCircuitPoint C L W Z hW hZ hencoded) = conjugationCoordinates W := by
  ext p r
  rw [circuitConjugationCoordinates_apply,
    (actualCircuitPoint_logical C L W Z hW hZ hencoded).1,
    (actualCircuitPoint_logical C L W Z hW hZ hencoded).2]
  rfl

/-- Logical matrices realized by any circuit with one specified support
arrangement. Gate values are unrestricted. -/
def supportLogicalMatrices (C : Code n dim ℓ g) (q : ℕ)
    (support : GateIndex n h → Finset (Fin n)) : Set (Operator (Fin ℓ)) :=
  {W | ∃ L : Circuit n dim q h,
    layoutSupport L = support ∧ Implements C (circuitEval L) W}

theorem supportLogicalMatrices_projective_finite
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hℓ : 2 ≤ ℓ) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (support : GateIndex n h → Finset (Fin n)) :
    (projectiveClass '' supportLogicalMatrices C q support).Finite := by
  classical
  letI : Nonempty (Fin ℓ) := ⟨⟨0, by omega⟩⟩
  apply finite_projectiveImage_of_finite_conjugationCoordinates
    (supportLogicalMatrices C q support)
  · rintro W ⟨L, _hSupport, hImpl⟩
    exact hImpl.1
  · by_cases hreal : ∃ L : Circuit n dim q h, layoutSupport L = support
    · obtain ⟨L₀, rfl⟩ := hreal
      apply (circuitConjugationCoordinates_range_finite C hDetect hg hq hcone L₀).subset
      rintro A ⟨W, hW, rfl⟩
      obtain ⟨L, hSupport, hImpl⟩ := hW
      obtain ⟨hWU, Z, hZU, hencoded⟩ := hImpl
      rw [← hSupport]
      exact ⟨actualCircuitPoint C L W Z hWU hZU hencoded,
        circuitConjugationCoordinates_actualCircuitPoint C L W Z hWU hZU hencoded⟩
    · apply (Set.finite_empty : (∅ : Set (Operator (Fin ℓ × Fin ℓ))).Finite).subset
      rintro A ⟨W, ⟨L, hSupport, _hImpl⟩, _hA⟩
      exact False.elim (hreal ⟨L, hSupport⟩)

/-- Finiteness for every support arrangement under the numerical cone
criterion, including arbitrary finite unary depth. -/
theorem logicalImage_finite_of_cone
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hℓ : 2 ≤ ℓ) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d) :
    (logicalImage C q h).Finite := by
  classical
  have hEach : ∀ support : GateIndex n h → Finset (Fin n),
      (projectiveClass '' supportLogicalMatrices C q support).Finite :=
    supportLogicalMatrices_projective_finite C hDetect hℓ hg hq hcone
  have hUnion :
      (⋃ support : GateIndex n h → Finset (Fin n),
        projectiveClass '' supportLogicalMatrices C q support).Finite :=
    Set.finite_iUnion hEach
  apply hUnion.subset
  rintro a ⟨L, W, hImpl, rfl⟩
  apply Set.mem_iUnion.mpr
  exact ⟨layoutSupport L, W, ⟨L, rfl, hImpl⟩, rfl⟩

/-- The full proposition recorded as `Manuscript.theoremOne`, with its
original dimension, distance, depth, and arity guards. -/
theorem theoremOne_proved : theoremOne := by
  intro n ℓ g d dim _hn hℓ hg hd C hDetect q h hdepth
  rcases hdepth with ⟨hq, hh⟩ | hq
  · exact logicalImage_finite_of_cone C hDetect hℓ hg (by omega)
      ((Arithmetic.below_threshold_iff q d h hq).mp hh)
  · subst q
    exact logicalImage_finite_of_cone C hDetect hℓ hg (by decide)
      (Arithmetic.unary_cone_bound d h hd)

/-- Non-density of the same logical image in the actual projective
unitary quotient, with exactly the declared Theorem 1 hypotheses. -/
theorem theoremOne_nondense
    (n ℓ g d : ℕ) (dim : Fin n → ℕ) (hn : 1 ≤ n) (hℓ : 2 ≤ ℓ)
    (hg : 1 ≤ g) (hd : 2 ≤ d) (C : Code n dim ℓ g) (hDetect : DetectsBelow C d)
    (q h : ℕ) (hdepth : (2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) :
    ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' logicalImage C q h) :=
  logicalImage_not_dense_in_projectiveUnitary C hℓ
    (theoremOne_proved n ℓ g d dim hn hℓ hg hd C hDetect q h hdepth)

end CriticalDepth.Manuscript
