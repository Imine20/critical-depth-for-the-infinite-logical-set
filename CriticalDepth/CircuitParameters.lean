import CriticalDepth.Support
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# A polynomial presentation containing every circuit on one support arrangement

Forward gates and inverse gates have independent local matrix variables.
Logical and gauge factors also have independent inverse variables. The
relations impose two-sided inverses and both encoded intertwining equations.
These are definitions of the proposed algebraic presentation. The actual
unitary-evaluation correspondence and its derivation-vanishing theorem are
separate open proof obligations, not assumptions of a claimed main proof.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

abbrev GateIndex (n h : ℕ) := Fin h × Fin n

abbrev CircuitVariable {n : ℕ} (dim : Fin n → ℕ) (K g h : ℕ)
    (support : GateIndex n h → Finset (Fin n)) :=
  (Σ p : GateIndex n h,
    Bool × LocalBasis dim (support p) × LocalBasis dim (support p)) ⊕
  (Bool × Fin K × Fin K) ⊕ (Bool × Fin g × Fin g)

/-- Coefficient-wise extension of an actual local complex-matrix basis. -/
def coefficientEmbed {n : ℕ} {dim : Fin n → ℕ} {R : Type*}
    [CommRing R] [Algebra ℂ R] (S : Finset (Fin n))
    (A : Matrix (LocalBasis dim S) (LocalBasis dim S) R) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) R :=
  ∑ a, ∑ b, A a b •
    (localEmbed S (Matrix.single a b (1 : ℂ))).map (algebraMap ℂ R)

section Presentation

variable {n K g h : ℕ} {dim : Fin n → ℕ}
variable (support : GateIndex n h → Finset (Fin n))

abbrev CircuitPolynomial := MvPolynomial (CircuitVariable dim K g h support) ℂ

def localGatePolynomial (p : GateIndex n h) (inverse : Bool) :
    Matrix (LocalBasis dim (support p)) (LocalBasis dim (support p))
      (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  fun a b => MvPolynomial.X (.inl ⟨p, inverse, a, b⟩)

def physicalGatePolynomial (p : GateIndex n h) (inverse : Bool) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  coefficientEmbed (support p) (localGatePolynomial support p inverse)

def logicalPolynomial (inverse : Bool) :
    Matrix (Fin K) (Fin K) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  fun a b => MvPolynomial.X (.inr (.inl (inverse, a, b)))

def gaugePolynomial (inverse : Bool) :
    Matrix (Fin g) (Fin g) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  fun a b => MvPolynomial.X (.inr (.inr (inverse, a, b)))

def executionGateIndices : List (GateIndex n h) :=
  (List.ofFn fun layer : Fin h => List.ofFn fun slot : Fin n => (layer, slot)).flatten

def totalPolynomial :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  ((executionGateIndices (n := n) (h := h)).map
    (fun p => physicalGatePolynomial support p false)).reverse.prod

def inverseTotalPolynomial :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  ((executionGateIndices (n := n) (h := h)).map
    (fun p => physicalGatePolynomial support p true)).prod

def matrixRelationEntries {ι κ : Type*}
    (A B : Matrix ι κ (CircuitPolynomial (dim := dim) (K := K) (g := g) support)) : Set (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  Set.range fun p : ι × κ => A p.1 p.2 - B p.1 p.2

def inverseRelationEntries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (CircuitPolynomial (dim := dim) (K := K) (g := g) support)) : Set (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  matrixRelationEntries support (A * B) 1 ∪
    matrixRelationEntries support (B * A) 1

def circuitRelations (C : Code n dim K g) : Set (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  (⋃ p : GateIndex n h,
    inverseRelationEntries support (physicalGatePolynomial support p false)
      (physicalGatePolynomial support p true)) ∪
  inverseRelationEntries support (logicalPolynomial support false) (logicalPolynomial support true) ∪
  inverseRelationEntries support (gaugePolynomial support false) (gaugePolynomial support true) ∪
  matrixRelationEntries support
    (totalPolynomial support * C.encoding.map MvPolynomial.C)
    (C.encoding.map MvPolynomial.C *
      (logicalPolynomial support false ⊗ₖ gaugePolynomial support false)) ∪
  matrixRelationEntries support
    (C.encoding.conjTranspose.map MvPolynomial.C * totalPolynomial support)
    ((logicalPolynomial support false ⊗ₖ gaugePolynomial support false) *
      C.encoding.conjTranspose.map MvPolynomial.C)

def circuitIdeal (C : Code n dim K g) : Ideal (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  Ideal.span (circuitRelations support C)

abbrev CircuitCoordinateRing (C : Code n dim K g) :=
  CircuitPolynomial (dim := dim) (K := K) (g := g) support ⧸ circuitIdeal support C

end Presentation

end CriticalDepth.Manuscript
