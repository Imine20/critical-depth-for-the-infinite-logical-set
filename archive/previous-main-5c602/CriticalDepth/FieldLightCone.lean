import CriticalDepth.ScalarExtension
import CriticalDepth.AlgebraicFrame

/-!
# Actual inverse-pair light cones over extension fields

The complex layer supplies only the finite site layout, disjointness, and arity.
The field-valued gates and inverse gates have concrete supported-span proofs.
There is no conjugation or Hermitian operation on the extension field.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {K : Type*} [Field K] [Algebra ℂ K]
variable {n q : ℕ} {dim : Fin n → ℕ}

theorem supportedSpan_mul_same {S : Finset (Fin n)}
    {A B : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hA : A ∈ supportedSpan (K := K) S) (hB : B ∈ supportedSpan (K := K) S) :
    A * B ∈ supportedSpan (K := K) S := by
  simpa only [Finset.union_self] using supportedSpan_mul hA hB

theorem supportedSpan_pair_conjugate_disjoint {S T : Finset (Fin n)}
    {O U Ui : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) (hU : U ∈ supportedSpan (K := K) T)
    (hST : Disjoint S T) (hUUi : U * Ui = 1) : U * O * Ui = O := by
  have hc : O * U = U * O := supportedSpan_commute hO hU hST
  rw [← hc, mul_assoc, hUUi, mul_one]

/-- Field-valued gates on a genuine disjoint complex support layout. -/
structure FieldLayer (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  layout : Layer n dim q
  gate : Fin n → GateWithInverse (PhysicalBasis n dim) K
  gate_locality : ∀ i, (gate i).1 ∈ supportedSpan (K := K) (layout.support i)
  inverse_locality : ∀ i, (gate i).2 ∈ supportedSpan (K := K) (layout.support i)
  inverse_identities : ∀ i, (gate i).1 * (gate i).2 = 1 ∧
    (gate i).2 * (gate i).1 = 1

def FieldLayer.eval (L : FieldLayer (K := K) n dim q) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K :=
  gatePairProduct (List.ofFn L.gate).reverse

def FieldLayer.evalInv (L : FieldLayer (K := K) n dim q) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K :=
  gatePairInverseProduct (List.ofFn L.gate).reverse

def FieldLayer.lightCone (L : FieldLayer (K := K) n dim q) (S : Finset (Fin n)) :
    Finset (Fin n) := L.layout.lightCone S

theorem FieldLayer.mutual_inverse (L : FieldLayer (K := K) n dim q) :
    L.eval * L.evalInv = 1 ∧ L.evalInv * L.eval = 1 := by
  apply gatePairProduct_mutual_inverse
  intro p hp
  have hp' : ∃ i, L.gate i = p := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hp
  obtain ⟨i, rfl⟩ := hp'
  exact L.inverse_identities i

theorem FieldLayer.logarithmic_gate_mem (L : FieldLayer (K := K) n dim q)
    (D : Derivation ℂ K K) (i : Fin n) :
    matrixDerivation D (L.gate i).1 * (L.gate i).2 ∈
      supportedSpan (K := K) (L.layout.support i) := by
  exact supportedSpan_mul_same
    (matrixDerivation_mem_supportedSpan D (L.gate_locality i)) (L.inverse_locality i)

theorem FieldLayer.backward_logarithmic_gate_mem (L : FieldLayer (K := K) n dim q)
    (D : Derivation ℂ K K) (i : Fin n) :
    (L.gate i).2 * matrixDerivation D (L.gate i).1 ∈
      supportedSpan (K := K) (L.layout.support i) := by
  exact supportedSpan_mul_same (L.inverse_locality i)
    (matrixDerivation_mem_supportedSpan D (L.gate_locality i))

private theorem supportedSpan_conjugate_pairProduct
    (gates : List (GateWithInverse (PhysicalBasis n dim) K)) (S : Finset (Fin n))
    (hstep : ∀ p ∈ gates, ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S → p.1 * O * p.2 ∈ supportedSpan (K := K) S) :
    ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S →
      gatePairProduct gates * O * gatePairInverseProduct gates ∈
        supportedSpan (K := K) S := by
  revert hstep
  induction gates with
  | nil =>
      intro hstep O hO
      simpa using hO
  | cons p gates ih =>
      intro hstep O hO
      have hg : ∀ r ∈ gates,
          ∀ P : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
          P ∈ supportedSpan (K := K) S →
          r.1 * P * r.2 ∈ supportedSpan (K := K) S := by
        intro r hr P hP
        exact hstep r (by simp [hr]) P hP
      have hinner := ih hg O hO
      have houter := hstep p (by simp) _ hinner
      simpa only [gatePairProduct_cons, gatePairInverseProduct_cons, mul_assoc]
        using houter

private theorem supportedSpan_inverse_conjugate_pairProduct
    (gates : List (GateWithInverse (PhysicalBasis n dim) K)) (S : Finset (Fin n))
    (hstep : ∀ p ∈ gates, ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S → p.2 * O * p.1 ∈ supportedSpan (K := K) S) :
    ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S →
      gatePairInverseProduct gates * O * gatePairProduct gates ∈
        supportedSpan (K := K) S := by
  revert hstep
  induction gates with
  | nil =>
      intro hstep O hO
      simpa using hO
  | cons p gates ih =>
      intro hstep O hO
      have hg : ∀ r ∈ gates,
          ∀ P : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
          P ∈ supportedSpan (K := K) S →
          r.2 * P * r.1 ∈ supportedSpan (K := K) S := by
        intro r hr P hP
        exact hstep r (by simp [hr]) P hP
      have hinner := hstep p (by simp) O hO
      have houter := ih hg _ hinner
      simpa only [gatePairProduct_cons, gatePairInverseProduct_cons, mul_assoc]
        using houter

/-- Forward conjugation has the same selective cone as the actual physical layout. -/
theorem FieldLayer.conjugate_mem_supportedSpan (L : FieldLayer (K := K) n dim q)
    (S : Finset (Fin n)) {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    L.eval * O * L.evalInv ∈ supportedSpan (K := K) (L.lightCone S) := by
  classical
  apply supportedSpan_conjugate_pairProduct (List.ofFn L.gate).reverse (L.lightCone S)
    ?_ O (supportedSpan_mono Finset.subset_union_left hO)
  intro p hp P hP
  have hp' : ∃ i, L.gate i = p := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hp
  obtain ⟨i, rfl⟩ := hp'
  rcases L.layout.support_subset_lightCone_or_disjoint S i with hsub | hdis
  · have hu := supportedSpan_mono hsub (L.gate_locality i)
    have hui := supportedSpan_mono hsub (L.inverse_locality i)
    exact supportedSpan_mul_same (supportedSpan_mul_same hu hP) hui
  · rw [supportedSpan_pair_conjugate_disjoint hP (L.gate_locality i)
      hdis.symm (L.inverse_identities i).1]
    exact hP

/-- Backward conjugation uses the actual inverse product, with no reordered premise. -/
theorem FieldLayer.inverse_conjugate_mem_supportedSpan
    (L : FieldLayer (K := K) n dim q) (S : Finset (Fin n))
    {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    L.evalInv * O * L.eval ∈ supportedSpan (K := K) (L.lightCone S) := by
  classical
  apply supportedSpan_inverse_conjugate_pairProduct (List.ofFn L.gate).reverse
    (L.lightCone S) ?_ O (supportedSpan_mono Finset.subset_union_left hO)
  intro p hp P hP
  have hp' : ∃ i, L.gate i = p := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hp
  obtain ⟨i, rfl⟩ := hp'
  rcases L.layout.support_subset_lightCone_or_disjoint S i with hsub | hdis
  · have hu := supportedSpan_mono hsub (L.gate_locality i)
    have hui := supportedSpan_mono hsub (L.inverse_locality i)
    exact supportedSpan_mul_same (supportedSpan_mul_same hui hP) hu
  · rw [supportedSpan_pair_conjugate_disjoint hP (L.inverse_locality i)
      hdis.symm (L.inverse_identities i).2]
    exact hP

theorem FieldLayer.lightCone_card_le (L : FieldLayer (K := K) n dim q)
    (S : Finset (Fin n)) (hq : 1 ≤ q) : (L.lightCone S).card ≤ q * S.card :=
  L.layout.lightCone_card_le S hq

def fieldLayerSequenceEval : List (FieldLayer (K := K) n dim q) →
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K
  | [] => 1
  | L :: layers => fieldLayerSequenceEval layers * L.eval

def fieldLayerSequenceInv : List (FieldLayer (K := K) n dim q) →
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K
  | [] => 1
  | L :: layers => L.evalInv * fieldLayerSequenceInv layers

def fieldLayerSequenceCone : List (FieldLayer (K := K) n dim q) →
    Finset (Fin n) → Finset (Fin n)
  | [], S => S
  | L :: layers, S => fieldLayerSequenceCone layers (L.lightCone S)

def fieldLayerSequenceBackwardCone : List (FieldLayer (K := K) n dim q) →
    Finset (Fin n) → Finset (Fin n)
  | [], S => S
  | L :: layers, S => L.lightCone (fieldLayerSequenceBackwardCone layers S)

theorem fieldLayerSequence_mutual_inverse (layers : List (FieldLayer (K := K) n dim q)) :
    fieldLayerSequenceEval layers * fieldLayerSequenceInv layers = 1 ∧
      fieldLayerSequenceInv layers * fieldLayerSequenceEval layers = 1 := by
  induction layers with
  | nil => simp [fieldLayerSequenceEval, fieldLayerSequenceInv]
  | cons L layers ih =>
      obtain ⟨hL, hLi⟩ := L.mutual_inverse
      obtain ⟨hR, hRi⟩ := ih
      constructor
      · calc
          fieldLayerSequenceEval (L :: layers) * fieldLayerSequenceInv (L :: layers) =
              fieldLayerSequenceEval layers * (L.eval * L.evalInv) *
                fieldLayerSequenceInv layers := by
            simp only [fieldLayerSequenceEval, fieldLayerSequenceInv, mul_assoc]
          _ = 1 := by rw [hL, mul_one, hR]
      · calc
          fieldLayerSequenceInv (L :: layers) * fieldLayerSequenceEval (L :: layers) =
              L.evalInv * (fieldLayerSequenceInv layers * fieldLayerSequenceEval layers) *
                L.eval := by
            simp only [fieldLayerSequenceEval, fieldLayerSequenceInv, mul_assoc]
          _ = 1 := by rw [hRi, mul_one, hLi]

theorem fieldLayerSequence_conjugate_mem
    (layers : List (FieldLayer (K := K) n dim q)) (S : Finset (Fin n))
    {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    fieldLayerSequenceEval layers * O * fieldLayerSequenceInv layers ∈
      supportedSpan (K := K) (fieldLayerSequenceCone layers S) := by
  induction layers generalizing S O with
  | nil => simpa [fieldLayerSequenceEval, fieldLayerSequenceInv, fieldLayerSequenceCone] using hO
  | cons L layers ih =>
      have hinner := L.conjugate_mem_supportedSpan S hO
      have houter := ih (L.lightCone S) hinner
      simpa only [fieldLayerSequenceEval, fieldLayerSequenceInv, fieldLayerSequenceCone,
        mul_assoc] using houter

theorem fieldLayerSequence_inverse_conjugate_mem
    (layers : List (FieldLayer (K := K) n dim q)) (S : Finset (Fin n))
    {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    fieldLayerSequenceInv layers * O * fieldLayerSequenceEval layers ∈
      supportedSpan (K := K) (fieldLayerSequenceBackwardCone layers S) := by
  induction layers generalizing S O with
  | nil =>
      simpa [fieldLayerSequenceEval, fieldLayerSequenceInv, fieldLayerSequenceBackwardCone] using hO
  | cons L layers ih =>
      have hinner := ih S hO
      have houter := L.inverse_conjugate_mem_supportedSpan
        (fieldLayerSequenceBackwardCone layers S) hinner
      simpa only [fieldLayerSequenceEval, fieldLayerSequenceInv,
        fieldLayerSequenceBackwardCone, mul_assoc] using houter

theorem fieldLayerSequenceCone_card_le (layers : List (FieldLayer (K := K) n dim q))
    (S : Finset (Fin n)) (hq : 1 ≤ q) :
    (fieldLayerSequenceCone layers S).card ≤ q ^ layers.length * S.card := by
  induction layers generalizing S with
  | nil => simp [fieldLayerSequenceCone]
  | cons L layers ih =>
      calc
        (fieldLayerSequenceCone (L :: layers) S).card =
            (fieldLayerSequenceCone layers (L.lightCone S)).card := rfl
        _ ≤ q ^ layers.length * (L.lightCone S).card := ih (L.lightCone S)
        _ ≤ q ^ layers.length * (q * S.card) :=
          Nat.mul_le_mul_left _ (L.lightCone_card_le S hq)
        _ = q ^ (L :: layers).length * S.card := by
          simp only [List.length_cons, pow_succ]
          ring

theorem fieldLayerSequenceBackwardCone_card_le
    (layers : List (FieldLayer (K := K) n dim q)) (S : Finset (Fin n)) (hq : 1 ≤ q) :
    (fieldLayerSequenceBackwardCone layers S).card ≤ q ^ layers.length * S.card := by
  induction layers generalizing S with
  | nil => simp [fieldLayerSequenceBackwardCone]
  | cons L layers ih =>
      calc
        (fieldLayerSequenceBackwardCone (L :: layers) S).card =
            (L.lightCone (fieldLayerSequenceBackwardCone layers S)).card := rfl
        _ ≤ q * (fieldLayerSequenceBackwardCone layers S).card :=
          L.lightCone_card_le _ hq
        _ ≤ q * (q ^ layers.length * S.card) := Nat.mul_le_mul_left q (ih S)
        _ = q ^ (L :: layers).length * S.card := by
          simp only [List.length_cons, pow_succ]
          ring

end CriticalDepth.Manuscript
