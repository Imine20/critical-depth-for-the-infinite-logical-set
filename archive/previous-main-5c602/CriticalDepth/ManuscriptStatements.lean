import CriticalDepth.MatrixCore
import CriticalDepth.Arithmetic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Concrete manuscript objects and original proof obligations

Source SHA-256: ec18f629bd6bfc770f470d71ed995de2743d1bf1368dfee7a4366edb43ac3138.
The definitions `theoremOne` and `theoremTwo` below RECORD propositions. They
are not proof declarations, axioms, or accepted proofs of the manuscript.
Their status remains open until separately named theorems establish them.

All matrix scalars are complex. The physical tensor basis retains every site.
Logical equivalence removes one global unit-modulus scalar. Correctability
quantifies over every supported operator, not just Pauli operators.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker BigOperators

abbrev PhysicalBasis (n : ℕ) (dim : Fin n → ℕ) := (i : Fin n) → Fin (dim i)

abbrev LocalBasis {n : ℕ} (dim : Fin n → ℕ) (S : Finset (Fin n)) :=
  (i : S) → Fin (dim i.1)

/-- Exact tensor-local embedding, with the identity on every complementary site. -/
def localEmbed {n : ℕ} {dim : Fin n → ℕ} (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) : Operator (PhysicalBasis n dim) := by
  classical
  exact fun x y =>
    if ∀ i, i ∉ S → x i = y i then
      A (fun i => x i.1) (fun i => y i.1)
    else 0

def SupportedOn {n : ℕ} {dim : Fin n → ℕ}
    (O : Operator (PhysicalBasis n dim)) (S : Finset (Fin n)) : Prop :=
  ∃ A : Operator (LocalBasis dim S), O = localEmbed S A

/-- The logical index precedes the gauge index, as in V : H_L ⊗ H_G → H. -/
structure Code (n : ℕ) (dim : Fin n → ℕ) (K g : ℕ) where
  encoding : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ
  isometry : encoding.conjTranspose * encoding = 1

def GaugeOnly {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (O : Operator (PhysicalBasis n dim)) : Prop :=
  ∃ M : Operator (Fin g),
    C.encoding.conjTranspose * O * C.encoding = (1 : Operator (Fin K)) ⊗ₖ M

def DetectsBelow {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card < d →
    ∀ O : Operator (PhysicalBasis n dim), SupportedOn O S → GaugeOnly C O

/-- Actual distance includes an undetectable operator of precisely this weight. -/
def HasActualDistance {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (d : ℕ) : Prop :=
  DetectsBelow C d ∧ ∃ S : Finset (Fin n), S.card = d ∧
    ∃ O : Operator (PhysicalBasis n dim), SupportedOn O S ∧ ¬ GaugeOnly C O

def Implements {n K g : ℕ} {dim : Fin n → ℕ} (C : Code n dim K g)
    (U : Operator (PhysicalBasis n dim)) (W : Operator (Fin K)) : Prop :=
  IsUnitary W ∧ ∃ Z : Operator (Fin g), IsUnitary Z ∧
    U * C.encoding = C.encoding * (W ⊗ₖ Z)

/-- At most n nonempty, disjoint gates, padded by supported identity gates.
The equivalence to arbitrary finite gate lists is an explicit open bridge. -/
structure Layer (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  support : Fin n → Finset (Fin n)
  gate : Fin n → Operator (PhysicalBasis n dim)
  disjoint : ∀ i j, i ≠ j → Disjoint (support i) (support j)
  arity : ∀ i, (support i).card ≤ q
  locality : ∀ i, SupportedOn (gate i) (support i)
  unitary : ∀ i, IsUnitary (gate i)

def Layer.eval {n q : ℕ} {dim : Fin n → ℕ} (L : Layer n dim q) :
    Operator (PhysicalBasis n dim) := (List.ofFn L.gate).reverse.prod

abbrev Circuit (n : ℕ) (dim : Fin n → ℕ) (q h : ℕ) := Fin h → Layer n dim q

def circuitEval {n q h : ℕ} {dim : Fin n → ℕ} (c : Circuit n dim q h) :
    Operator (PhysicalBasis n dim) := (List.ofFn fun i => (c i).eval).reverse.prod

def logicalImage {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (q h : ℕ) : Set (ProjectiveOperator (Fin K)) :=
  {a | ∃ c : Circuit n dim q h, ∃ W : Operator (Fin K),
    Implements C (circuitEval c) W ∧ projectiveClass W = a}

/-- Source Theorem 1, lines 253–265: primary finiteness claim, including q=1.
The finite-list/padded-layer bridge and non-density corollary remain obligations. -/
def theoremOne : Prop :=
  ∀ (n K g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ K → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim K g, DetectsBelow C d →
      ∀ q h : ℕ,
        ((2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) →
        (logicalImage C q h).Finite

def hInfinity {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, r = (h : ℕ∞) ∧ (logicalImage C q h).Infinite}

abbrev QubitBasis (n : ℕ) := PhysicalBasis n (fun _ => 2)

inductive SinglePauli where
  | I | X | Y | Z
  deriving DecidableEq

instance : Fintype SinglePauli where
  elems := {.I, .X, .Y, .Z}
  complete p := by cases p <;> simp

def SinglePauli.matrix : SinglePauli → Operator (Fin 2)
  | .I => 1
  | .X => !![0, 1; 1, 0]
  | .Y => !![0, -Complex.I; Complex.I, 0]
  | .Z => !![1, 0; 0, -1]

def pauliMatrix {n : ℕ} (phase : Fin 4) (p : Fin n → SinglePauli) :
    Operator (QubitBasis n) :=
  fun x y => Complex.I ^ phase.val * ∏ i, (p i).matrix (x i) (y i)

def IsPauli {n : ℕ} (U : Operator (QubitBasis n)) : Prop :=
  ∃ phase : Fin 4, ∃ p : Fin n → SinglePauli, U = pauliMatrix phase p

/-- Stabilizer subspace as the simultaneous +1 eigenspace of a Pauli subgroup. -/
def IsStabilizer {n k : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1) : Prop :=
  ∃ S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ),
    (∀ U ∈ S, IsPauli (U : Operator (QubitBasis n))) ∧
    Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v}

def HasContinuousLogicalSubgroup {n K : ℕ} (C : Code n (fun _ => 2) K 1)
    (q h : ℕ) : Prop :=
  ∃ W : ℝ → Operator (Fin K), Continuous W ∧
    (∀ t, IsUnitary (W t)) ∧ W 0 = 1 ∧
    (∀ s t, W (s + t) = W s * W t) ∧
    (∃ t, ¬ ProjectivelyEquivalent (W t) 1) ∧
    (∀ t, projectiveClass (W t) ∈ logicalImage C q h)

/-- Source Theorem 2, lines 403–412. This is an OPEN proposition, not a proof. -/
def theoremTwo : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinity C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
        HasContinuousLogicalSubgroup C q (Arithmetic.criticalDepth q d)

end CriticalDepth.Manuscript
