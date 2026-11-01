import CriticalDepth.LocalScalarCoordinates
import CriticalDepth.FieldLightCone
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Field-valued solutions of the actual circuit presentation

Every relation below is obtained by evaluating a generator of the defining
ideal. Physical inverse pairs, the two encoded intertwining equations, and
concrete tensor-support membership are proved from that presentation.
No inverse equation for the unembedded local matrices is asserted.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

section MatrixEvaluation

variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)

theorem solutionMap_mul {ι κ μ : Type*} [Fintype κ]
    (M : Matrix ι κ A) (N : Matrix κ μ A) :
    (M * N).map φ = M.map φ * N.map φ := by
  ext i j
  change φ (∑ k, M i k * N k j) = ∑ k, φ (M i k) * φ (N k j)
  simp only [map_sum, map_mul]

theorem solutionMap_one {ι : Type*} [DecidableEq ι] :
    (1 : Matrix ι ι A).map φ = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]

theorem solutionMap_kronecker {ι κ μ ν : Type*}
    (M : Matrix ι κ A) (N : Matrix μ ν A) :
    (M ⊗ₖ N).map φ = M.map φ ⊗ₖ N.map φ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact map_mul φ (M i j) (N a b)

theorem solutionMap_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrices : List (Matrix ι ι A)) :
    matrices.prod.map φ = (matrices.map fun M => M.map φ).prod := by
  induction matrices with
  | nil => simpa only [List.prod_nil, List.map_nil] using solutionMap_one φ
  | cons M matrices ih =>
      simpa only [List.prod_cons, List.map_cons, solutionMap_mul, ih]

end MatrixEvaluation

section Solutions

variable {n ℓ g h : ℕ} {dim : Fin n → ℕ}
variable (C : Code n dim ℓ g)
variable (support : GateIndex n h → Finset (Fin n))
variable {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
variable (ψ : CircuitCoordinateRing (C := C) (support := support) →ₐ[ℂ] 𝕂)

/-- The presentation has finitely many matrix-entry variables. -/
instance circuitCoordinateRing_isNoetherianRing :
    IsNoetherianRing (CircuitCoordinateRing (C := C) (support := support)) := by
  classical
  unfold CircuitCoordinateRing
  infer_instance

/-- Pull a coordinate-ring point back to the polynomial presentation. -/
def circuitPointMap :
    CircuitPolynomial (dim := dim) (K := ℓ) (g := g) support →ₐ[ℂ] 𝕂 :=
  ψ.comp (Ideal.Quotient.mkₐ ℂ (circuitIdeal support C))

theorem circuitPointMap_relation
    (f : CircuitPolynomial (K := ℓ) (g := g) support)
    (hf : f ∈ circuitRelations support C) : circuitPointMap C support ψ f = 0 := by
  have hi : f ∈ circuitIdeal support C := Ideal.subset_span hf
  change ψ (Ideal.Quotient.mk (circuitIdeal support C) f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hi, map_zero]

theorem circuitPointMap_matrixRelation {ι κ : Type*}
    (A B : Matrix ι κ (CircuitPolynomial (K := ℓ) (g := g) support))
    (hAB : matrixRelationEntries support A B ⊆ circuitRelations support C) :
    A.map (circuitPointMap C support ψ) = B.map (circuitPointMap C support ψ) := by
  ext i j
  change circuitPointMap C support ψ (A i j) = circuitPointMap C support ψ (B i j)
  have hf := circuitPointMap_relation C support ψ (A i j - B i j)
    (hAB ⟨(i, j), rfl⟩)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hf)

theorem circuitPointMap_inverseRelations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (CircuitPolynomial (K := ℓ) (g := g) support))
    (hAB : inverseRelationEntries support A B ⊆ circuitRelations support C) :
    A.map (circuitPointMap C support ψ) * B.map (circuitPointMap C support ψ) = 1 ∧
      B.map (circuitPointMap C support ψ) * A.map (circuitPointMap C support ψ) = 1 := by
  constructor
  · have heq := circuitPointMap_matrixRelation C support ψ (A * B) 1
      (fun f hf => hAB (Set.mem_union_left _ hf))
    simpa only [solutionMap_mul, solutionMap_one] using heq
  · have heq := circuitPointMap_matrixRelation C support ψ (B * A) 1
      (fun f hf => hAB (Set.mem_union_right _ hf))
    simpa only [solutionMap_mul, solutionMap_one] using heq

private theorem physicalInverseRelations_subset (p : GateIndex n h) :
    inverseRelationEntries support (physicalGatePolynomial support p false)
      (physicalGatePolynomial support p true) ⊆ circuitRelations support C := by
  intro f hf
  have hf0 : f ∈ (⋃ p : GateIndex n h,
      inverseRelationEntries support (physicalGatePolynomial support p false)
        (physicalGatePolynomial support p true)) := Set.mem_iUnion.mpr ⟨p, hf⟩
  simp only [circuitRelations, Set.mem_union]
  tauto

private theorem logicalInverseRelations_subset :
    inverseRelationEntries support (logicalPolynomial support false)
      (logicalPolynomial support true) ⊆ circuitRelations support C := by
  intro f hf
  simp only [circuitRelations, Set.mem_union]
  tauto

private theorem gaugeInverseRelations_subset :
    inverseRelationEntries support (gaugePolynomial support false)
      (gaugePolynomial support true) ⊆ circuitRelations support C := by
  intro f hf
  simp only [circuitRelations, Set.mem_union]
  tauto

def solutionGate (p : GateIndex n h) (inverse : Bool) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) 𝕂 :=
  (physicalGatePolynomial support p inverse).map (circuitPointMap C support ψ)

def solutionLogical (inverse : Bool) : Matrix (Fin ℓ) (Fin ℓ) 𝕂 :=
  (logicalPolynomial support inverse).map (circuitPointMap C support ψ)

def solutionGauge (inverse : Bool) : Matrix (Fin g) (Fin g) 𝕂 :=
  (gaugePolynomial support inverse).map (circuitPointMap C support ψ)

def solutionTotal : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) 𝕂 :=
  (totalPolynomial support).map (circuitPointMap C support ψ)

def solutionInverseTotal : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) 𝕂 :=
  (inverseTotalPolynomial support).map (circuitPointMap C support ψ)

theorem solutionGate_inverse (p : GateIndex n h) :
    solutionGate C support ψ p false * solutionGate C support ψ p true = 1 ∧
      solutionGate C support ψ p true * solutionGate C support ψ p false = 1 := by
  exact circuitPointMap_inverseRelations C support ψ _ _
    (physicalInverseRelations_subset C support p)

theorem solutionLogical_inverse :
    solutionLogical C support ψ false * solutionLogical C support ψ true = 1 ∧
      solutionLogical C support ψ true * solutionLogical C support ψ false = 1 := by
  exact circuitPointMap_inverseRelations C support ψ _ _
    (logicalInverseRelations_subset C support)

theorem solutionGauge_inverse :
    solutionGauge C support ψ false * solutionGauge C support ψ true = 1 ∧
      solutionGauge C support ψ true * solutionGauge C support ψ false = 1 := by
  exact circuitPointMap_inverseRelations C support ψ _ _
    (gaugeInverseRelations_subset C support)

theorem solutionGate_mem_supportedSpan (p : GateIndex n h) (inverse : Bool) :
    solutionGate C support ψ p inverse ∈ supportedSpan (K := 𝕂) (support p) :=
  physicalGatePolynomial_map_mem_supportedSpan support p inverse (circuitPointMap C support ψ)

theorem circuitPointMap_constant {ι κ : Type*} (A : Matrix ι κ ℂ) :
    (A.map MvPolynomial.C).map (circuitPointMap C support ψ) =
      A.map (algebraMap ℂ 𝕂) := by
  ext i j
  exact (circuitPointMap C support ψ).commutes (A i j)

theorem solution_encoding :
    solutionTotal C support ψ * C.encoding.map (algebraMap ℂ 𝕂) =
      C.encoding.map (algebraMap ℂ 𝕂) *
        (solutionLogical C support ψ false ⊗ₖ solutionGauge C support ψ false) := by
  have hsub : matrixRelationEntries support
      (totalPolynomial support * C.encoding.map MvPolynomial.C)
      (C.encoding.map MvPolynomial.C *
        (logicalPolynomial support false ⊗ₖ gaugePolynomial support false)) ⊆
      circuitRelations support C := by
    intro f hf
    simp only [circuitRelations, Set.mem_union]
    tauto
  have heq := circuitPointMap_matrixRelation C support ψ _ _ hsub
  simpa only [solutionMap_mul, solutionMap_kronecker, circuitPointMap_constant,
    solutionTotal, solutionLogical, solutionGauge] using heq

theorem solution_encoding_dual :
    C.encoding.conjTranspose.map (algebraMap ℂ 𝕂) * solutionTotal C support ψ =
      (solutionLogical C support ψ false ⊗ₖ solutionGauge C support ψ false) *
        C.encoding.conjTranspose.map (algebraMap ℂ 𝕂) := by
  have hsub : matrixRelationEntries support
      (C.encoding.conjTranspose.map MvPolynomial.C * totalPolynomial support)
      ((logicalPolynomial support false ⊗ₖ gaugePolynomial support false) *
        C.encoding.conjTranspose.map MvPolynomial.C) ⊆ circuitRelations support C := by
    intro f hf
    simp only [circuitRelations, Set.mem_union]
    tauto
  have heq := circuitPointMap_matrixRelation C support ψ _ _ hsub
  simpa only [solutionMap_mul, solutionMap_kronecker, circuitPointMap_constant,
    solutionTotal, solutionLogical, solutionGauge] using heq

theorem solution_encoding_isometry :
    C.encoding.conjTranspose.map (algebraMap ℂ 𝕂) *
      C.encoding.map (algebraMap ℂ 𝕂) = 1 := by
  have heq := congrArg (fun A : Matrix (Fin ℓ × Fin g) (Fin ℓ × Fin g) ℂ =>
    A.map (algebraMap ℂ 𝕂)) C.isometry
  simpa only [constantMatrix_mul, constantMatrix_one] using heq

def solutionGateList : List (GateWithInverse (PhysicalBasis n dim) 𝕂) :=
  (executionGateIndices (n := n) (h := h)).map fun p =>
    (solutionGate C support ψ p false, solutionGate C support ψ p true)

theorem solutionTotal_eq_gatePairProduct :
    solutionTotal C support ψ = gatePairProduct (solutionGateList C support ψ).reverse := by
  unfold solutionTotal totalPolynomial gatePairProduct solutionGateList
  rw [solutionMap_list_prod]
  simp [solutionGate, List.map_reverse, List.map_map, Function.comp_def]

theorem solutionInverseTotal_eq_gatePairInverseProduct :
    solutionInverseTotal C support ψ =
      gatePairInverseProduct (solutionGateList C support ψ).reverse := by
  unfold solutionInverseTotal inverseTotalPolynomial gatePairInverseProduct solutionGateList
  rw [solutionMap_list_prod]
  simp [solutionGate, List.map_map, Function.comp_def]

theorem solutionTotal_inverse :
    solutionTotal C support ψ * solutionInverseTotal C support ψ = 1 ∧
      solutionInverseTotal C support ψ * solutionTotal C support ψ = 1 := by
  rw [solutionTotal_eq_gatePairProduct, solutionInverseTotal_eq_gatePairInverseProduct]
  apply gatePairProduct_mutual_inverse
  intro pair hp
  have hp' : ∃ p, (solutionGate C support ψ p false,
      solutionGate C support ψ p true) = pair := by
    obtain ⟨p, _hp, heq⟩ := List.mem_map.mp
      (show pair ∈ solutionGateList C support ψ from List.mem_reverse.mp hp)
    exact ⟨p, heq⟩
  obtain ⟨p, rfl⟩ := hp'
  exact solutionGate_inverse C support ψ p

end Solutions

section LayoutSolutions

variable {n ℓ g h q : ℕ} {dim : Fin n → ℕ}
variable (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
variable {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]

def layoutSupport : GateIndex n h → Finset (Fin n) := fun p => (L p.1).support p.2

/-- A field-valued layer with precisely the supplied physical support layout. -/
def solutionFieldLayer
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (layer : Fin h) : FieldLayer (K := 𝕂) n dim q where
  layout := L layer
  gate := fun i => (solutionGate C (layoutSupport L) ψ (layer, i) false,
    solutionGate C (layoutSupport L) ψ (layer, i) true)
  gate_locality := fun i => solutionGate_mem_supportedSpan C (layoutSupport L) ψ (layer, i) false
  inverse_locality := fun i => solutionGate_mem_supportedSpan C (layoutSupport L) ψ (layer, i) true
  inverse_identities := fun i => solutionGate_inverse C (layoutSupport L) ψ (layer, i)

theorem solutionFieldLayer_eval
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (layer : Fin h) :
    (solutionFieldLayer C L ψ layer).eval =
      (List.ofFn fun i => solutionGate C (layoutSupport L) ψ (layer, i) false).reverse.prod := by
  simp [FieldLayer.eval, gatePairProduct, solutionFieldLayer, List.map_reverse,
    Function.comp_def]

theorem solutionFieldLayer_evalInv
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (layer : Fin h) :
    (solutionFieldLayer C L ψ layer).evalInv =
      (List.ofFn fun i => solutionGate C (layoutSupport L) ψ (layer, i) true).prod := by
  simp [FieldLayer.evalInv, gatePairInverseProduct, solutionFieldLayer, Function.comp_def]

private theorem map_executionGateIndices {α : Type*} (f : GateIndex n h → α) :
    (executionGateIndices (n := n) (h := h)).map f =
      (List.ofFn fun layer : Fin h => List.ofFn fun i : Fin n => f (layer, i)).flatten := by
  simp [executionGateIndices, List.map_flatten, List.map_ofFn, Function.comp_def]

private theorem list_reverse_prod_flatten {M : Type*} [Monoid M] (lists : List (List M)) :
    lists.flatten.reverse.prod = (lists.map fun xs => xs.reverse.prod).reverse.prod := by
  induction lists with
  | nil => simp
  | cons xs lists ih => simp [List.reverse_append, List.prod_append, ih]

private theorem list_prod_flatten {M : Type*} [Monoid M] (lists : List (List M)) :
    lists.flatten.prod = (lists.map List.prod).prod := by
  induction lists with
  | nil => simp
  | cons xs lists ih => simp [List.prod_append, ih]

private theorem solution_fieldSequenceEval_eq_reverse_prod
    (layers : List (FieldLayer (K := 𝕂) n dim q)) :
    fieldLayerSequenceEval layers = (layers.map FieldLayer.eval).reverse.prod := by
  induction layers with
  | nil => simp [fieldLayerSequenceEval]
  | cons layer layers ih =>
      simp [fieldLayerSequenceEval, ih, List.reverse_cons, List.prod_append]

private theorem solution_fieldSequenceInv_eq_prod
    (layers : List (FieldLayer (K := 𝕂) n dim q)) :
    fieldLayerSequenceInv layers = (layers.map FieldLayer.evalInv).prod := by
  induction layers with
  | nil => simp [fieldLayerSequenceInv]
  | cons layer layers ih => simp [fieldLayerSequenceInv, ih]

/-- The polynomial total uses exactly the same layer and slot order as the
actual field-valued layer sequence. -/
theorem solutionTotal_eq_fieldLayerSequence
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂) :
    solutionTotal C (layoutSupport L) ψ =
      fieldLayerSequenceEval (List.ofFn (solutionFieldLayer C L ψ)) := by
  rw [solution_fieldSequenceEval_eq_reverse_prod]
  unfold solutionTotal totalPolynomial
  rw [solutionMap_list_prod]
  simp only [List.map_reverse, List.map_map]
  change ((executionGateIndices (n := n) (h := h)).map
    (fun p => solutionGate C (layoutSupport L) ψ p false)).reverse.prod = _
  rw [map_executionGateIndices, list_reverse_prod_flatten]
  simp only [List.map_ofFn, solutionFieldLayer_eval, Function.comp_def]

/-- The inverse polynomial total has the corresponding unreversed inverse
execution order. -/
theorem solutionInverseTotal_eq_fieldLayerSequence
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂) :
    solutionInverseTotal C (layoutSupport L) ψ =
      fieldLayerSequenceInv (List.ofFn (solutionFieldLayer C L ψ)) := by
  rw [solution_fieldSequenceInv_eq_prod]
  unfold solutionInverseTotal inverseTotalPolynomial
  rw [solutionMap_list_prod]
  simp only [List.map_map]
  change ((executionGateIndices (n := n) (h := h)).map
    (fun p => solutionGate C (layoutSupport L) ψ p true)).prod = _
  rw [map_executionGateIndices, list_prod_flatten]
  simp only [List.map_ofFn, solutionFieldLayer_evalInv, Function.comp_def]

end LayoutSolutions

end CriticalDepth.Manuscript
