import CriticalDepth.CircuitSolutions
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual complex circuits give points of the coordinate algebra

Local witnesses come from the supplied layer locality proofs. Their adjoints
provide inverse coordinates; no unembedded local inverse equation is needed.
The two encoded relations follow from the original encoded unitary action.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

variable {n ℓ g h q : ℕ} {dim : Fin n → ℕ}

def pointLocalGate (L : Fin h → Layer n dim q) (p : GateIndex n h) :
    Operator (LocalBasis dim (layoutSupport L p)) :=
  Classical.choose ((L p.1).locality p.2)

theorem pointLocalGate_embed (L : Fin h → Layer n dim q) (p : GateIndex n h) :
    localEmbed (layoutSupport L p) (pointLocalGate L p) = (L p.1).gate p.2 :=
  (Classical.choose_spec ((L p.1).locality p.2)).symm

def actualCircuitAssignment (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    CircuitVariable dim ℓ g h (layoutSupport L) → ℂ
  | .inl ⟨p, false, a, b⟩ => pointLocalGate L p a b
  | .inl ⟨p, true, a, b⟩ => (pointLocalGate L p).conjTranspose a b
  | .inr (.inl (false, a, b)) => W a b
  | .inr (.inl (true, a, b)) => W.conjTranspose a b
  | .inr (.inr (false, a, b)) => Z a b
  | .inr (.inr (true, a, b)) => Z.conjTranspose a b

def actualPolynomialPoint (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    CircuitPolynomial (dim := dim) (K := ℓ) (g := g) (layoutSupport L) →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (actualCircuitAssignment L W Z)

theorem point_localPolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (localGatePolynomial (layoutSupport L) p false).map (actualPolynomialPoint L W Z) =
      pointLocalGate L p := by
  ext a b
  simp [localGatePolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_localPolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (localGatePolynomial (layoutSupport L) p true).map (actualPolynomialPoint L W Z) =
      (pointLocalGate L p).conjTranspose := by
  ext a b
  simp [localGatePolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_physicalPolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (physicalGatePolynomial (layoutSupport L) p false).map (actualPolynomialPoint L W Z) =
      (L p.1).gate p.2 := by
  rw [physicalGatePolynomial, coefficientEmbed_naturality,
    point_localPolynomial_forward, coefficientEmbed_complex, pointLocalGate_embed]

theorem point_physicalPolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (physicalGatePolynomial (layoutSupport L) p true).map (actualPolynomialPoint L W Z) =
      ((L p.1).gate p.2).conjTranspose := by
  rw [physicalGatePolynomial, coefficientEmbed_naturality,
    point_localPolynomial_inverse, coefficientEmbed_complex,
    localEmbed_conjTranspose, pointLocalGate_embed]

theorem point_logicalPolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (logicalPolynomial (layoutSupport L) false).map (actualPolynomialPoint L W Z) = W := by
  ext a b
  simp [logicalPolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_logicalPolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (logicalPolynomial (layoutSupport L) true).map (actualPolynomialPoint L W Z) =
      W.conjTranspose := by
  ext a b
  simp [logicalPolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_gaugePolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (gaugePolynomial (layoutSupport L) false).map (actualPolynomialPoint L W Z) = Z := by
  ext a b
  simp [gaugePolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_gaugePolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (gaugePolynomial (layoutSupport L) true).map (actualPolynomialPoint L W Z) =
      Z.conjTranspose := by
  ext a b
  simp [gaugePolynomial, actualPolynomialPoint, actualCircuitAssignment]

private theorem point_map_executionGateIndices {α : Type*} (f : GateIndex n h → α) :
    (executionGateIndices (n := n) (h := h)).map f =
      (List.ofFn fun layer : Fin h => List.ofFn fun slot : Fin n => f (layer, slot)).flatten := by
  simp [executionGateIndices, List.map_flatten, List.map_ofFn, Function.comp_def]

private theorem point_reverse_prod_flatten {M : Type*} [Monoid M] (lists : List (List M)) :
    lists.flatten.reverse.prod = (lists.map fun xs => xs.reverse.prod).reverse.prod := by
  induction lists with
  | nil => simp
  | cons xs lists ih => simp [List.reverse_append, List.prod_append, ih]

theorem point_circuitEval_execution (L : Fin h → Layer n dim q) :
    circuitEval L = ((executionGateIndices (n := n) (h := h)).map
      (fun p => (L p.1).gate p.2)).reverse.prod := by
  rw [point_map_executionGateIndices, point_reverse_prod_flatten]
  simp only [circuitEval, Layer.eval, List.map_ofFn, Function.comp_def]

theorem point_totalPolynomial (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (totalPolynomial (layoutSupport L)).map (actualPolynomialPoint L W Z) = circuitEval L := by
  unfold totalPolynomial
  rw [solutionMap_list_prod]
  simp only [List.map_reverse, List.map_map, Function.comp_def,
    point_physicalPolynomial_forward]
  exact (point_circuitEval_execution L).symm

private theorem point_conjTranspose_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrices : List (Operator ι)) :
    matrices.prod.conjTranspose = (matrices.reverse.map Matrix.conjTranspose).prod := by
  induction matrices with
  | nil => simp
  | cons A matrices ih =>
      simp [Matrix.conjTranspose_mul, ih, List.reverse_cons, List.map_append, List.prod_append]

theorem point_inverseTotalPolynomial (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (inverseTotalPolynomial (layoutSupport L)).map (actualPolynomialPoint L W Z) =
      (circuitEval L).conjTranspose := by
  unfold inverseTotalPolynomial
  rw [solutionMap_list_prod, point_circuitEval_execution, point_conjTranspose_list_prod]
  simp only [List.reverse_reverse, List.map_map, Function.comp_def,
    point_physicalPolynomial_inverse]

private theorem point_isUnitary_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Operator ι) (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A * B) := by
  constructor
  · calc
      star (A * B) * (A * B) = star B * (star A * A) * B := by
        simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hA.1, mul_one, hB.1]
  · calc
      (A * B) * star (A * B) = A * (B * star B) * star A := by
        simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hB.2, mul_one, hA.2]

private theorem point_isUnitary_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrices : List (Operator ι)) (hunit : ∀ A ∈ matrices, IsUnitary A) :
    IsUnitary matrices.prod := by
  revert hunit
  induction matrices with
  | nil => intro hunit; constructor <;> simp
  | cons A matrices ih =>
      intro hunit
      exact point_isUnitary_mul A matrices.prod (hunit A (by simp))
        (ih (fun B hB => hunit B (by simp [hB])))

theorem point_circuitEval_isUnitary (L : Fin h → Layer n dim q) : IsUnitary (circuitEval L) := by
  rw [point_circuitEval_execution]
  apply point_isUnitary_list_prod
  intro U hU
  obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hU)
  exact (L p.1).unitary p.2

private theorem point_star_kronecker {ι κ : Type*}
    (W : Operator ι) (Z : Operator κ) : star (W ⊗ₖ Z) = star W ⊗ₖ star Z := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change star (W j i * Z b a) = star (W j i) * star (Z b a)
  rw [star_mul]
  ring

theorem point_kronecker_isUnitary {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (W : Operator ι) (Z : Operator κ) (hW : IsUnitary W) (hZ : IsUnitary Z) :
    IsUnitary (W ⊗ₖ Z) := by
  constructor
  · rw [point_star_kronecker, ← Matrix.mul_kronecker_mul, hW.1, hZ.1,
      Matrix.one_kronecker_one]
  · rw [point_star_kronecker, ← Matrix.mul_kronecker_mul, hW.2, hZ.2,
      Matrix.one_kronecker_one]

theorem point_encoded_dual (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    C.encoding.conjTranspose * circuitEval L = (W ⊗ₖ Z) * C.encoding.conjTranspose := by
  let U := circuitEval L
  let T := W ⊗ₖ Z
  have hU : IsUnitary U := point_circuitEval_isUnitary L
  have hT : IsUnitary T := point_kronecker_isUnitary W Z hW hZ
  have hadj : C.encoding.conjTranspose * star U = star T * C.encoding.conjTranspose := by
    change C.encoding.conjTranspose * (circuitEval L).conjTranspose =
      (W ⊗ₖ Z).conjTranspose * C.encoding.conjTranspose
    have heq := congrArg Matrix.conjTranspose hencoded
    simpa only [Matrix.conjTranspose_mul] using heq
  change C.encoding.conjTranspose * U = T * C.encoding.conjTranspose
  calc
    C.encoding.conjTranspose * U =
        ((T * star T) * C.encoding.conjTranspose) * U := by rw [hT.2]; simp
    _ = T * (star T * C.encoding.conjTranspose) * U := by
      simp only [Matrix.mul_assoc]
    _ = T * (C.encoding.conjTranspose * star U) * U := by rw [← hadj]
    _ = T * C.encoding.conjTranspose := by
      simp only [Matrix.mul_assoc, hU.1, Matrix.mul_one]

private theorem point_constantPolynomial (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g))
    {ι κ : Type*} (A : Matrix ι κ ℂ) :
    (A.map MvPolynomial.C).map (actualPolynomialPoint L W Z) = A := by
  ext i j
  simpa using (actualPolynomialPoint L W Z).commutes (A i j)

private theorem point_matrixRelation_vanish (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) {ι κ : Type*}
    (A B : Matrix ι κ (CircuitPolynomial (K := ℓ) (g := g) (layoutSupport L)))
    (heq : A.map (actualPolynomialPoint L W Z) = B.map (actualPolynomialPoint L W Z)) :
    ∀ f ∈ matrixRelationEntries (layoutSupport L) A B, actualPolynomialPoint L W Z f = 0 := by
  rintro f ⟨⟨i, j⟩, rfl⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg (fun M => M i j) heq)

private theorem point_inverseRelation_vanish (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (CircuitPolynomial (K := ℓ) (g := g) (layoutSupport L)))
    (hinv : A.map (actualPolynomialPoint L W Z) * B.map (actualPolynomialPoint L W Z) = 1 ∧
      B.map (actualPolynomialPoint L W Z) * A.map (actualPolynomialPoint L W Z) = 1) :
    ∀ f ∈ inverseRelationEntries (layoutSupport L) A B,
      actualPolynomialPoint L W Z f = 0 := by
  intro f hf
  rcases hf with hf | hf
  · apply point_matrixRelation_vanish L W Z (A * B) 1 ?_ f hf
    simpa only [solutionMap_mul, solutionMap_one] using hinv.1
  · apply point_matrixRelation_vanish L W Z (B * A) 1 ?_ f hf
    simpa only [solutionMap_mul, solutionMap_one] using hinv.2

/-- Every generator of the defining ideal vanishes at the actual circuit
assignment. The dual relation is derived from the original unitary action. -/
theorem actualPolynomialPoint_relations
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    ∀ f ∈ circuitRelations (layoutSupport L) C, actualPolynomialPoint L W Z f = 0 := by
  intro f hf
  simp only [circuitRelations, Set.mem_union, Set.mem_iUnion] at hf
  rcases hf with (((hphysical | hlogical) | hgauge) | hencoding) | hdual
  · obtain ⟨p, hp⟩ := hphysical
    apply point_inverseRelation_vanish L W Z _ _ ?_ f hp
    rw [point_physicalPolynomial_forward, point_physicalPolynomial_inverse]
    exact ⟨((L p.1).unitary p.2).2, ((L p.1).unitary p.2).1⟩
  · apply point_inverseRelation_vanish L W Z _ _ ?_ f hlogical
    rw [point_logicalPolynomial_forward, point_logicalPolynomial_inverse]
    exact ⟨hW.2, hW.1⟩
  · apply point_inverseRelation_vanish L W Z _ _ ?_ f hgauge
    rw [point_gaugePolynomial_forward, point_gaugePolynomial_inverse]
    exact ⟨hZ.2, hZ.1⟩
  · apply point_matrixRelation_vanish L W Z _ _ ?_ f hencoding
    simpa only [solutionMap_mul, point_constantPolynomial, point_totalPolynomial,
      solutionMap_kronecker, point_logicalPolynomial_forward,
      point_gaugePolynomial_forward] using hencoded
  · apply point_matrixRelation_vanish L W Z _ _ ?_ f hdual
    simpa only [solutionMap_mul, point_constantPolynomial, point_totalPolynomial,
      solutionMap_kronecker, point_logicalPolynomial_forward,
      point_gaugePolynomial_forward] using point_encoded_dual C L W Z hW hZ hencoded

theorem actualPolynomialPoint_ideal
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    ∀ f, f ∈ circuitIdeal (layoutSupport L) C → actualPolynomialPoint L W Z f = 0 := by
  have hker : circuitIdeal (layoutSupport L) C ≤
      RingHom.ker (actualPolynomialPoint L W Z).toRingHom := by
    apply Ideal.span_le.mpr
    intro f hf
    change actualPolynomialPoint L W Z f = 0
    exact actualPolynomialPoint_relations C L W Z hW hZ hencoded f hf
  intro f hf
  exact hker hf

/-- The actual complex circuit, logical unitary, and gauge unitary give an
algebra-homomorphism point of the coordinate algebra. -/
def actualCircuitPoint
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (circuitIdeal (layoutSupport L) C) (actualPolynomialPoint L W Z)
    (actualPolynomialPoint_ideal C L W Z hW hZ hencoded)

@[simp] theorem actualCircuitPoint_quotient
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z))
    (f : CircuitPolynomial (K := ℓ) (g := g) (layoutSupport L)) :
    actualCircuitPoint C L W Z hW hZ hencoded
      (Ideal.Quotient.mk (circuitIdeal (layoutSupport L) C) f) = actualPolynomialPoint L W Z f := by
  exact AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp (circuitIdeal (layoutSupport L) C)
      (actualPolynomialPoint L W Z) (actualPolynomialPoint_ideal C L W Z hW hZ hencoded)) f

theorem circuitPointMap_actualCircuitPoint
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    circuitPointMap C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) =
      actualPolynomialPoint L W Z := by
  exact Ideal.Quotient.liftₐ_comp (circuitIdeal (layoutSupport L) C)
    (actualPolynomialPoint L W Z) (actualPolynomialPoint_ideal C L W Z hW hZ hencoded)

theorem actualCircuitPoint_logical
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    solutionLogical C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) false = W ∧
      solutionLogical C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) true =
        W.conjTranspose := by
  constructor
  · unfold solutionLogical
    rw [circuitPointMap_actualCircuitPoint]
    exact point_logicalPolynomial_forward L W Z
  · unfold solutionLogical
    rw [circuitPointMap_actualCircuitPoint]
    exact point_logicalPolynomial_inverse L W Z

theorem actualCircuitPoint_gauge
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    solutionGauge C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) false = Z ∧
      solutionGauge C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) true =
        Z.conjTranspose := by
  constructor
  · unfold solutionGauge
    rw [circuitPointMap_actualCircuitPoint]
    exact point_gaugePolynomial_forward L W Z
  · unfold solutionGauge
    rw [circuitPointMap_actualCircuitPoint]
    exact point_gaugePolynomial_inverse L W Z

theorem actualCircuitPoint_total
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    solutionTotal C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) = circuitEval L := by
  unfold solutionTotal
  rw [circuitPointMap_actualCircuitPoint]
  exact point_totalPolynomial L W Z

end CriticalDepth.Manuscript
