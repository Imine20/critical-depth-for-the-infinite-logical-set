import CriticalDepth.FieldLightCone

/-!
# Concrete layer derivatives and the two-sided same-layer support endpoint

Disjoint gates in one layer do not enlarge one another's logarithmic insertions.
The derivative identities below use the actual gate/inverse lists and their
explicit physical execution order.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {K : Type*} [Field K] [Algebra ℂ K]
variable {n q : ℕ} {dim : Fin n → ℕ}

/-- A layer's own gate support is unchanged by its selective light cone. -/
theorem Layer.lightCone_support (L : Layer n dim q) (j : Fin n) :
    L.lightCone (L.support j) = L.support j := by
  classical
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with hxj | hxA
    · exact hxj
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxA
      have hact : ¬ Disjoint (L.support i) (L.support j) :=
        (Finset.mem_filter.mp hi).2
      by_cases hij : i = j
      · simpa only [hij] using hxi
      · exact False.elim (hact (L.disjoint i j hij))
  · exact Finset.subset_union_left

theorem FieldLayer.conjugate_gateSupport_mem (L : FieldLayer (K := K) n dim q)
    (j : Fin n) {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) (L.layout.support j)) :
    L.eval * O * L.evalInv ∈ supportedSpan (K := K) (L.layout.support j) := by
  simpa only [FieldLayer.lightCone, Layer.lightCone_support] using
    L.conjugate_mem_supportedSpan (L.layout.support j) hO

theorem FieldLayer.inverse_conjugate_gateSupport_mem (L : FieldLayer (K := K) n dim q)
    (j : Fin n) {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) (L.layout.support j)) :
    L.evalInv * O * L.eval ∈ supportedSpan (K := K) (L.layout.support j) := by
  simpa only [FieldLayer.lightCone, Layer.lightCone_support] using
    L.inverse_conjugate_mem_supportedSpan (L.layout.support j) hO

theorem FieldLayer.backward_conjugated_logarithmic_gate_mem
    (L : FieldLayer (K := K) n dim q) (D : Derivation ℂ K K) (j : Fin n) :
    L.evalInv * (matrixDerivation D (L.gate j).1 * (L.gate j).2) * L.eval ∈
      supportedSpan (K := K) (L.layout.support j) := by
  exact L.inverse_conjugate_gateSupport_mem j (L.logarithmic_gate_mem D j)

private theorem conjugate_list_sum
    (indices : List (Fin n))
    (H : Fin n → Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K)
    (U Ui : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K)
    (h : ∀ j ∈ indices, U * H j * Ui = H j) :
    U * (indices.map H).sum * Ui = (indices.map H).sum := by
  revert h
  induction indices with
  | nil =>
      intro h
      simp
  | cons j indices ih =>
      intro h
      have hj := h j (by simp)
      have hr : ∀ k ∈ indices, U * H k * Ui = H k := by
        intro k hk
        exact h k (by simp [hk])
      simp only [List.map_cons, List.sum_cons, mul_add, add_mul, hj, ih hr]

private theorem indexed_layer_logarithmic_derivative
    (L : FieldLayer (K := K) n dim q) (D : Derivation ℂ K K)
    (indices : List (Fin n)) (hn : indices.Nodup) :
    matrixDerivation D (gatePairProduct (indices.map L.gate)) *
        gatePairInverseProduct (indices.map L.gate) =
      (indices.map fun j => matrixDerivation D (L.gate j).1 * (L.gate j).2).sum := by
  revert hn
  induction indices with
  | nil =>
      intro hn
      simp [matrixDerivation_one]
  | cons i indices ih =>
      intro hn
      have hi : i ∉ indices := (List.nodup_cons.mp hn).1
      have hr : indices.Nodup := (List.nodup_cons.mp hn).2
      have hg : ∀ p ∈ indices.map L.gate, p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 := by
        intro p hp
        obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hp
        exact L.inverse_identities j
      have hprod := (gatePairProduct_mutual_inverse (indices.map L.gate) hg).1
      have hfixed : ∀ j ∈ indices,
          (L.gate i).1 * (matrixDerivation D (L.gate j).1 * (L.gate j).2) *
            (L.gate i).2 = matrixDerivation D (L.gate j).1 * (L.gate j).2 := by
        intro j hj
        have hji : j ≠ i := by
          intro hji
          subst j
          exact hi hj
        exact supportedSpan_pair_conjugate_disjoint (L.logarithmic_gate_mem D j)
          (L.gate_locality i) (L.layout.disjoint j i hji) (L.inverse_identities i).1
      simp only [List.map_cons, gatePairProduct_cons, gatePairInverseProduct_cons,
        List.sum_cons]
      rw [logarithmic_product_rule D (L.gate i).1 (gatePairProduct (indices.map L.gate))
        (L.gate i).2 (gatePairInverseProduct (indices.map L.gate)) hprod, ih hr]
      rw [conjugate_list_sum indices
        (fun j => matrixDerivation D (L.gate j).1 * (L.gate j).2)
        (L.gate i).1 (L.gate i).2 hfixed]

private theorem sum_ofFn_eq_fintype_sum {M : Type*} [AddCommMonoid M]
    {m : ℕ} (f : Fin m → M) : (List.ofFn f).sum = ∑ i, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      exact congrArg (fun z => f 0 + z) (ih (fun i => f i.succ))

/-- The genuine layer derivative is the finite sum of local gate insertions. -/
theorem FieldLayer.logarithmic_derivative_eq_sum (L : FieldLayer (K := K) n dim q)
    (D : Derivation ℂ K K) :
    matrixDerivation D L.eval * L.evalInv =
      ∑ j : Fin n, matrixDerivation D (L.gate j).1 * (L.gate j).2 := by
  classical
  let indices : List (Fin n) := (List.ofFn fun j : Fin n => j).reverse
  have hn' : (List.ofFn fun j : Fin n => j).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj hij
    have hij' := congrArg Fin.val hij
    simpa only [List.getElem_ofFn] using hij'
  have hn : indices.Nodup := by
    simpa only [indices, List.nodup_reverse] using hn'
  have hg : indices.map L.gate = (List.ofFn L.gate).reverse := by
    simp [indices, List.map_reverse, List.map_ofFn, Function.comp_def]
  have hs : (indices.map fun j => matrixDerivation D (L.gate j).1 * (L.gate j).2).sum =
      ∑ j : Fin n, matrixDerivation D (L.gate j).1 * (L.gate j).2 := by
    simp only [indices, List.map_reverse, List.sum_reverse, List.map_ofFn,
      Function.comp_def]
    exact sum_ofFn_eq_fintype_sum _
  have hh := indexed_layer_logarithmic_derivative L D indices hn
  rw [hg, hs] at hh
  exact hh

/-- An actual gate insertion, conjugated by all physically later layers. -/
def layerGateInsertionAt (D : Derivation ℂ K K) :
    (layers : List (FieldLayer (K := K) n dim q)) → Fin layers.length → Fin n →
      Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K
  | [], i => Fin.elim0 i
  | L :: layers, i =>
      Fin.cases
        (fun j => fieldLayerSequenceEval layers *
          (matrixDerivation D (L.gate j).1 * (L.gate j).2) * fieldLayerSequenceInv layers)
        (fun r => layerGateInsertionAt D layers r) i

theorem layerGateInsertion_sum_cons (D : Derivation ℂ K K)
    (L : FieldLayer (K := K) n dim q) (layers : List (FieldLayer (K := K) n dim q)) :
    (∑ r : Fin (L :: layers).length, ∑ j : Fin n, layerGateInsertionAt D (L :: layers) r j) =
      fieldLayerSequenceEval layers *
          (∑ j : Fin n, matrixDerivation D (L.gate j).1 * (L.gate j).2) *
            fieldLayerSequenceInv layers +
        ∑ r : Fin layers.length, ∑ j : Fin n, layerGateInsertionAt D layers r j := by
  change (∑ r : Fin (layers.length + 1),
    ∑ j : Fin n, layerGateInsertionAt D (L :: layers) r j) = _
  rw [Fin.sum_univ_succ]
  simp only [layerGateInsertionAt, Fin.cases_zero, Fin.cases_succ,
    Finset.mul_sum, Finset.sum_mul]

/-- The total derivative expansion is derived from the actual field-valued layers. -/
theorem fieldLayerSequence_logarithmic_derivative_eq_sum
    (D : Derivation ℂ K K) (layers : List (FieldLayer (K := K) n dim q)) :
    matrixDerivation D (fieldLayerSequenceEval layers) * fieldLayerSequenceInv layers =
      ∑ r : Fin layers.length, ∑ j : Fin n, layerGateInsertionAt D layers r j := by
  induction layers with
  | nil =>
      simp [fieldLayerSequenceEval, fieldLayerSequenceInv, matrixDerivation_one]
  | cons L layers ih =>
      rw [fieldLayerSequenceEval, fieldLayerSequenceInv,
        logarithmic_product_rule D (fieldLayerSequenceEval layers) L.eval
          (fieldLayerSequenceInv layers) L.evalInv L.mutual_inverse.1,
        L.logarithmic_derivative_eq_sum D, ih, layerGateInsertion_sum_cons]
      exact add_comm _ _

end CriticalDepth.Manuscript
