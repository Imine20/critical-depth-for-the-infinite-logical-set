import ReducedCircuitPresentation

/-!
The inverse circuit determines both factor inverses over the reduced ring.
-/

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

noncomputable section

variable {n K g h : ℕ} {dim : Fin n → ℕ}
variable (support : GateIndex n h → Finset (Fin n)) (C : Code n dim K g)

abbrev forwardCircuitEvaluation :
    CircuitPolynomial (dim := dim) (K := K) (g := g) support →ₐ[ℂ] ForwardCircuitRing support C :=
  (Ideal.Quotient.mkₐ ℂ (forwardCircuitIdeal support C)).comp (omitInverse support)

theorem forwardCircuitEvaluation_relation
    {p : CircuitPolynomial (dim := dim) (K := K) (g := g) support}
    (hp : p ∈ gateInverseEntries (dim := dim) (K := K) (g := g) support ∪ encodingEntries support C) :
    forwardCircuitEvaluation support C p = 0 := by
  change Ideal.Quotient.mk (forwardCircuitIdeal support C) (omitInverse support p) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨p, hp, rfl⟩)

theorem forwardCircuitEvaluation_matrixRelation {ι κ : Type*}
    (A B : Matrix ι κ (CircuitPolynomial (dim := dim) (K := K) (g := g) support))
    (hAB : matrixRelationEntries support A B ⊆
      gateInverseEntries (dim := dim) (K := K) (g := g) support ∪ encodingEntries support C) :
    A.map (forwardCircuitEvaluation support C) = B.map (forwardCircuitEvaluation support C) := by
  ext i j
  let f := forwardCircuitEvaluation support C
  change f (A i j) = f (B i j)
  rw [← sub_eq_zero, ← map_sub]
  exact forwardCircuitEvaluation_relation support C (hAB ⟨(i, j), rfl⟩)

theorem forwardCircuitEvaluation_gateInverse (p : GateIndex n h) :
    let a := forwardCircuitEvaluation support C
    let U := (physicalGatePolynomial support p false).map a
    let Ui := (physicalGatePolynomial support p true).map a
    U * Ui = 1 ∧ Ui * U = 1 := by
  intro a U Ui
  have hp : inverseRelationEntries support (physicalGatePolynomial support p false)
      (physicalGatePolynomial support p true) ⊆
      gateInverseEntries (dim := dim) (K := K) (g := g) support ∪ encodingEntries support C := by
    intro f hf
    exact Or.inl (Set.mem_iUnion.mpr ⟨p, hf⟩)
  constructor
  · have he := forwardCircuitEvaluation_matrixRelation support C _ _
      (fun f hf => hp (Set.mem_union_left _ hf))
    simpa only [solutionMap_mul, solutionMap_one] using he
  · have he := forwardCircuitEvaluation_matrixRelation support C _ _
      (fun f hf => hp (Set.mem_union_right _ hf))
    simpa only [solutionMap_mul, solutionMap_one] using he

theorem forwardCircuitEvaluation_totalInverse :
    let a := forwardCircuitEvaluation support C
    let U := (totalPolynomial support).map a
    let Ui := (inverseTotalPolynomial support).map a
    U * Ui = 1 ∧ Ui * U = 1 := by
  intro a U Ui
  let f (p : GateIndex n h) := (physicalGatePolynomial support p false).map a
  let g (p : GateIndex n h) := (physicalGatePolynomial support p true).map a
  have hProd (L : List (GateIndex n h)) :
      (L.map f).reverse.prod * (L.map g).prod = 1 ∧
        (L.map g).prod * (L.map f).reverse.prod = 1 := by
    induction L with
    | nil => simp
    | cons p L ih =>
      simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one]
      obtain ⟨hfg, hgf⟩ := forwardCircuitEvaluation_gateInverse support C p
      have hp : f p * g p = 1 := hfg
      have hp' : g p * f p = 1 := hgf
      constructor
      · rw [mul_assoc, ← mul_assoc (f p), hp, one_mul, ih.1]
      · rw [mul_assoc, ← mul_assoc ((L.map g).prod), ih.2, one_mul, hp']
  have hU : U = ((executionGateIndices (n := n) (h := h)).map f).reverse.prod := by
    unfold U totalPolynomial
    rw [solutionMap_list_prod a]
    simp only [List.map_reverse, List.map_map, Function.comp_def, f]
  have hUi : Ui = ((executionGateIndices (n := n) (h := h)).map g).prod := by
    unfold Ui inverseTotalPolynomial
    rw [solutionMap_list_prod a]
    simp only [List.map_map, Function.comp_def, g]
  rw [hU, hUi]
  exact hProd executionGateIndices

abbrev forwardLogical :=
  (logicalPolynomial (K := K) (g := g) support false).map (forwardCircuitEvaluation support C)

abbrev forwardGauge :=
  (gaugePolynomial (K := K) (g := g) support false).map (forwardCircuitEvaluation support C)

def forwardEncodedInverse :
    Matrix (Fin K × Fin g) (Fin K × Fin g) (ForwardCircuitRing support C) :=
  let a := forwardCircuitEvaluation support C
  (C.encoding.conjTranspose.map (algebraMap ℂ _)) *
    ((inverseTotalPolynomial support).map a) * (C.encoding.map (algebraMap ℂ _))

theorem forwardEncodedInverse_spec :
    let Q := forwardLogical support C ⊗ₖ forwardGauge support C
    forwardEncodedInverse support C * Q = 1 ∧ Q * forwardEncodedInverse support C = 1 := by
  intro Q
  let a := forwardCircuitEvaluation support C
  let V₀ : Matrix (PhysicalBasis n dim) (Fin K × Fin g)
      (CircuitPolynomial (dim := dim) (K := K) (g := g) support) := C.encoding.map MvPolynomial.C
  let E₀ : Matrix (Fin K × Fin g) (PhysicalBasis n dim)
      (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
    C.encoding.conjTranspose.map MvPolynomial.C
  let V := C.encoding.map (algebraMap ℂ (ForwardCircuitRing support C))
  let E := C.encoding.conjTranspose.map (algebraMap ℂ (ForwardCircuitRing support C))
  let U := (totalPolynomial support).map a
  let Ui := (inverseTotalPolynomial support).map a
  let Q₀ := logicalPolynomial (dim := dim) (K := K) (g := g) support false ⊗ₖ
    gaugePolynomial (dim := dim) (K := K) (g := g) support false
  have hV : V₀.map a = V := by ext i j; exact a.commutes _
  have hE : E₀.map a = E := by ext i j; exact a.commutes _
  have hQ : Q₀.map a = Q := solutionMap_kronecker a _ _
  have hEV : E * V = 1 := by
    let f := Algebra.ofId ℂ (ForwardCircuitRing support C)
    have he := congrArg (fun A : Matrix (Fin K × Fin g) (Fin K × Fin g) ℂ => A.map f) C.isometry
    rw [solutionMap_mul, solutionMap_one] at he
    exact he
  have hforward : U * V = V * Q := by
    have he := forwardCircuitEvaluation_matrixRelation support C (totalPolynomial support * V₀)
      (V₀ * Q₀) (fun r hr => Or.inr (Or.inl hr))
    change ((totalPolynomial support * V₀).map a) = ((V₀ * Q₀).map a) at he
    rw [solutionMap_mul, solutionMap_mul, hV, hQ] at he
    exact he
  have hdual : E * U = Q * E := by
    have he := forwardCircuitEvaluation_matrixRelation support C (E₀ * totalPolynomial support)
      (Q₀ * E₀) (fun r hr => Or.inr (Or.inr hr))
    change ((E₀ * totalPolynomial support).map a) = ((Q₀ * E₀).map a) at he
    rw [solutionMap_mul, solutionMap_mul, hE, hQ] at he
    exact he
  have hUi : U * Ui = 1 ∧ Ui * U = 1 := forwardCircuitEvaluation_totalInverse support C
  exact CriticalDepth.Manuscript20261114.encodedKronecker_inverse E V U Ui
    (forwardLogical support C) (forwardGauge support C) hEV hUi.1 hUi.2 hforward hdual

def forwardLogicalInverse (j : Fin g) : Matrix (Fin K) (Fin K) (ForwardCircuitRing support C) :=
  let B : Matrix (Fin K × Fin g) (Fin K × Fin g) (ForwardCircuitRing support C) :=
    ((1 : Matrix (Fin K) (Fin K) (ForwardCircuitRing support C)) ⊗ₖ forwardGauge support C) *
      forwardEncodedInverse support C
  fun a b => B (a, j) (b, j)

def forwardGaugeInverse (i : Fin K) : Matrix (Fin g) (Fin g) (ForwardCircuitRing support C) :=
  let B : Matrix (Fin K × Fin g) (Fin K × Fin g) (ForwardCircuitRing support C) :=
    (forwardLogical support C ⊗ₖ (1 : Matrix (Fin g) (Fin g) (ForwardCircuitRing support C))) *
      forwardEncodedInverse support C
  fun a b => B (i, a) (i, b)

theorem forwardFactorInverses_spec (i : Fin K) (j : Fin g) :
    let W := forwardLogical support C
    let Z := forwardGauge support C
    let Wi := forwardLogicalInverse support C j
    let Zi := forwardGaugeInverse support C i
    W * Wi = 1 ∧ Wi * W = 1 ∧ Z * Zi = 1 ∧ Zi * Z = 1 :=
  CriticalDepth.Manuscript20261114.kroneckerFactor_inverses i j
    (forwardLogical support C) (forwardGauge support C) (forwardEncodedInverse support C)
    (forwardEncodedInverse_spec support C).2

#print axioms forwardCircuitEvaluation_totalInverse
#print axioms forwardFactorInverses_spec

end
end CriticalDepth.Manuscript
