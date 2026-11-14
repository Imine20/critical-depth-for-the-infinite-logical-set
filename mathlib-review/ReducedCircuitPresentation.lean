import CriticalDepthMathlib
import EncodedInverse

/-!
# The circuit ring with only gate inverses as variables
-/

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

noncomputable section

variable {n K g h : ℕ} {dim : Fin n → ℕ}
variable (support : GateIndex n h → Finset (Fin n))

/-- The manuscript keeps inverse variables for local gates only. -/
abbrev ForwardCircuitVariable :=
  (Σ p : GateIndex n h,
    Bool × LocalBasis dim (support p) × LocalBasis dim (support p)) ⊕
    (Fin K × Fin K) ⊕ (Fin g × Fin g)

abbrev ForwardCircuitPolynomial :=
  MvPolynomial (ForwardCircuitVariable (dim := dim) (K := K) (g := g) support) ℂ

def includeForwardVariable :
    ForwardCircuitVariable (dim := dim) (K := K) (g := g) support →
      CircuitVariable dim K g h support
  | .inl p => .inl p
  | .inr (.inl p) => .inr (.inl (false, p))
  | .inr (.inr p) => .inr (.inr (false, p))

def includeForward :
    ForwardCircuitPolynomial (dim := dim) (K := K) (g := g) support →ₐ[ℂ]
      CircuitPolynomial (dim := dim) (K := K) (g := g) support :=
  MvPolynomial.rename (includeForwardVariable support)

def omitInverse :
    CircuitPolynomial (dim := dim) (K := K) (g := g) support →ₐ[ℂ]
      ForwardCircuitPolynomial (dim := dim) (K := K) (g := g) support :=
  MvPolynomial.aeval fun
    | .inl p => MvPolynomial.X (.inl p)
    | .inr (.inl (false, p)) => MvPolynomial.X (.inr (.inl p))
    | .inr (.inr (false, p)) => MvPolynomial.X (.inr (.inr p))
    | .inr (.inl (true, _)) | .inr (.inr (true, _)) => 0

theorem omitInverse_includeForward :
    (omitInverse (dim := dim) (K := K) (g := g) support).comp (includeForward support) =
      AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro p
  rcases p with p | p
  · simp [includeForward, omitInverse, includeForwardVariable]
  · rcases p with p | p <;> simp [includeForward, omitInverse, includeForwardVariable]

variable (C : Code n dim K g)

abbrev gateInverseEntries : Set (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  ⋃ p : GateIndex n h,
    inverseRelationEntries (K := K) (g := g) support
      (physicalGatePolynomial support p false) (physicalGatePolynomial support p true)

abbrev encodingEntries :=
  matrixRelationEntries support
    (totalPolynomial support * C.encoding.map MvPolynomial.C)
    (C.encoding.map MvPolynomial.C *
      (logicalPolynomial support false ⊗ₖ gaugePolynomial support false)) ∪
  matrixRelationEntries support
    (C.encoding.conjTranspose.map MvPolynomial.C * totalPolynomial support)
    ((logicalPolynomial support false ⊗ₖ gaugePolynomial support false) *
      C.encoding.conjTranspose.map MvPolynomial.C)

def forwardCircuitRelations :
    Set (ForwardCircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  omitInverse support '' (gateInverseEntries (dim := dim) (K := K) (g := g) support ∪ encodingEntries support C)

def forwardCircuitIdeal : Ideal (ForwardCircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  Ideal.span (forwardCircuitRelations support C)

abbrev ForwardCircuitRing :=
  ForwardCircuitPolynomial (dim := dim) (K := K) (g := g) support ⧸
    forwardCircuitIdeal support C

/-- A map agreeing on retained variables respects the local gate and encoding equations. -/
theorem circuitMaps_agree_on_forwardRelations
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (a : CircuitPolynomial (dim := dim) (K := K) (g := g) support →ₐ[ℂ] R)
    (b : CircuitPolynomial (dim := dim) (K := K) (g := g) support →ₐ[ℂ] R)
    (H : a.comp (includeForward support) = b.comp (includeForward support))
    {p : CircuitPolynomial (dim := dim) (K := K) (g := g) support}
    (hp : p ∈ gateInverseEntries (dim := dim) (K := K) (g := g) support ∪ encodingEntries support C) :
    a p = b p := by
  have hx (v : ForwardCircuitVariable (dim := dim) (K := K) (g := g) support) :
      a (MvPolynomial.X (includeForwardVariable support v)) =
        b (MvPolynomial.X (includeForwardVariable support v)) := by
    simpa [includeForward] using DFunLike.congr_fun H (MvPolynomial.X v)
  have hgate (k : GateIndex n h) (i : Bool) :
      (physicalGatePolynomial support k i).map a = (physicalGatePolynomial support k i).map b := by
    simp only [physicalGatePolynomial, coefficientEmbed_naturality]
    congr 1
    ext x y
    exact hx (.inl ⟨k, i, x, y⟩)
  have hW : (logicalPolynomial support false).map a = (logicalPolynomial support false).map b := by
    ext x y
    exact hx (.inr (.inl (x, y)))
  have hZ : (gaugePolynomial support false).map a = (gaugePolynomial support false).map b := by
    ext x y
    exact hx (.inr (.inr (x, y)))
  have hU : (totalPolynomial support).map a = (totalPolynomial support).map b := by
    let L := (executionGateIndices (n := n) (h := h)).reverse
    have hl : (L.map fun k => (physicalGatePolynomial support k false).map a) =
        L.map fun k => (physicalGatePolynomial support k false).map b := by
      exact List.map_congr_left (fun k _ => hgate k false)
    simpa only [L, totalPolynomial, solutionMap_list_prod, List.map_reverse,
      List.map_map, Function.comp_def] using congrArg List.prod hl
  have hconst {ι κ : Type} (A : Matrix ι κ ℂ) :
      (A.map MvPolynomial.C).map a = (A.map MvPolynomial.C).map b := by
    ext i j
    exact (a.commutes _).trans (b.commutes _).symm
  have hentry {ι κ : Type}
      (A B : Matrix ι κ (CircuitPolynomial (dim := dim) (K := K) (g := g) support))
      (ha : A.map a = A.map b) (hb : B.map a = B.map b)
      (hmem : p ∈ matrixRelationEntries support A B) : a p = b p := by
    obtain ⟨⟨i, j⟩, rfl⟩ := hmem
    simp only [map_sub]
    exact congrArg₂ (· - ·) (congrFun (congrFun ha i) j) (congrFun (congrFun hb i) j)
  have hV := hconst C.encoding
  have hE := hconst C.encoding.conjTranspose
  rcases hp with hp | hp
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    rcases hk with hk | hk
    · apply hentry _ _ _ _ hk
      · rw [solutionMap_mul, solutionMap_mul, hgate, hgate]
      · simp [solutionMap_one]
    · apply hentry _ _ _ _ hk
      · rw [solutionMap_mul, solutionMap_mul, hgate, hgate]
      · simp [solutionMap_one]
  · rcases hp with hp | hp
    · apply hentry _ _ _ _ hp
      · rw [solutionMap_mul, solutionMap_mul, hU, hV]
      · rw [solutionMap_mul, solutionMap_mul, solutionMap_kronecker,
          solutionMap_kronecker, hV, hW, hZ]
    · apply hentry _ _ _ _ hp
      · rw [solutionMap_mul, solutionMap_mul, hE, hU]
      · rw [solutionMap_mul, solutionMap_mul, solutionMap_kronecker,
          solutionMap_kronecker, hE, hW, hZ]

#print axioms omitInverse_includeForward
#print axioms circuitMaps_agree_on_forwardRelations

end
end CriticalDepth.Manuscript
