import CriticalDepth.Support
import CriticalDepth.LayerOperations
import CriticalDepth.DepthZero

/-!
# Arbitrary finite gate lists and the bounded slot model

The input layers have arbitrary finite lengths. Empty-support gates are
removed with their unit-modulus scalar recorded. The retained list keeps its
order and is padded with identity gates on empty supports. No physical site
or ancillary tensor factor is added, including when the register has no sites.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Classical Kronecker

variable {n q : ℕ} {dim : Fin n → ℕ}

structure ListGate (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  support : Finset (Fin n)
  gate : Operator (PhysicalBasis n dim)
  arity : support.card ≤ q
  locality : SupportedOn gate support
  unitary : IsUnitary gate

structure ArbitraryLayer (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  gates : List (ListGate n dim q)
  disjoint : gates.Pairwise (fun G H => Disjoint G.support H.support)

def identityListGate : ListGate n dim q where
  support := ∅
  gate := 1
  arity := by simp
  locality := supportedOn_one ∅
  unitary := isUnitary_one

def listGateEval (gates : List (ListGate n dim q)) : Operator (PhysicalBasis n dim) :=
  (gates.map ListGate.gate).reverse.prod

@[simp] theorem listGateEval_nil : listGateEval ([] : List (ListGate n dim q)) = 1 := by
  simp [listGateEval]

@[simp] theorem listGateEval_cons (G : ListGate n dim q) (gates : List (ListGate n dim q)) :
    listGateEval (G :: gates) = listGateEval gates * G.gate := by
  simp [listGateEval, List.reverse_cons, List.prod_append]

def ArbitraryLayer.eval (L : ArbitraryLayer n dim q) : Operator (PhysicalBasis n dim) :=
  listGateEval L.gates

/-- This recursive filter retains the original gate order. -/
def filterNonemptyGates : List (ListGate n dim q) → List (ListGate n dim q)
  | [] => []
  | G :: gates =>
      if G.support = ∅ then filterNonemptyGates gates
      else G :: filterNonemptyGates gates

theorem mem_filterNonemptyGates (G : ListGate n dim q) (gates : List (ListGate n dim q)) :
    G ∈ filterNonemptyGates gates ↔ G ∈ gates ∧ G.support ≠ ∅ := by
  induction gates with
  | nil => simp [filterNonemptyGates]
  | cons H gates ih =>
      by_cases hH : H.support = ∅
      · simp only [filterNonemptyGates, if_pos hH, ih, List.mem_cons]
        constructor
        · intro h
          exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨h | h, hne⟩
          · subst G
            exact False.elim (hne hH)
          · exact ⟨h, hne⟩
      · simp only [filterNonemptyGates, if_neg hH, List.mem_cons, ih]
        constructor
        · rintro (rfl | h)
          · exact ⟨Or.inl rfl, hH⟩
          · exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩

theorem filterNonemptyGates_pairwise (gates : List (ListGate n dim q))
    (h : gates.Pairwise (fun G H => Disjoint G.support H.support)) :
    (filterNonemptyGates gates).Pairwise (fun G H => Disjoint G.support H.support) := by
  revert h
  induction gates with
  | nil =>
      intro h
      simp [filterNonemptyGates]
  | cons G gates ih =>
      intro h
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      by_cases hG : G.support = ∅
      · simpa only [filterNonemptyGates, if_pos hG] using ih htail
      · rw [filterNonemptyGates, if_neg hG, List.pairwise_cons]
        refine ⟨?_, ih htail⟩
        intro H hH
        exact hhead H ((mem_filterNonemptyGates H gates).mp hH).1

def listGateSupportUnion : List (ListGate n dim q) → Finset (Fin n)
  | [] => ∅
  | G :: gates => G.support ∪ listGateSupportUnion gates

theorem mem_listGateSupportUnion (x : Fin n) (gates : List (ListGate n dim q)) :
    x ∈ listGateSupportUnion gates ↔ ∃ G ∈ gates, x ∈ G.support := by
  induction gates with
  | nil => simp [listGateSupportUnion]
  | cons G gates ih =>
      simp only [listGateSupportUnion, Finset.mem_union, ih, List.mem_cons]
      aesop

theorem nonemptyGateList_length_le_union_card (gates : List (ListGate n dim q))
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support))
    (hne : ∀ G ∈ gates, G.support ≠ ∅) :
    gates.length ≤ (listGateSupportUnion gates).card := by
  revert hpair hne
  induction gates with
  | nil =>
      intro hpair hne
      simp [listGateSupportUnion]
  | cons G gates ih =>
      intro hpair hne
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hG : G.support ≠ ∅ := hne G (by simp)
      have htailne : ∀ H ∈ gates, H.support ≠ ∅ := by
        intro H hH
        exact hne H (by simp [hH])
      have hbound := ih htail htailne
      have hdis : Disjoint G.support (listGateSupportUnion gates) := by
        apply Finset.disjoint_left.mpr
        intro x hx hxu
        obtain ⟨H, hH, hxH⟩ := (mem_listGateSupportUnion x gates).mp hxu
        exact Finset.disjoint_left.mp (hhead H hH) hx hxH
      have hpos : 0 < G.support.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hG)
      simp only [List.length_cons, listGateSupportUnion, Finset.card_union_of_disjoint hdis]
      omega

theorem filterNonemptyGates_length_le (L : ArbitraryLayer n dim q) :
    (filterNonemptyGates L.gates).length ≤ n := by
  calc
    (filterNonemptyGates L.gates).length ≤
        (listGateSupportUnion (filterNonemptyGates L.gates)).card :=
      nonemptyGateList_length_le_union_card _ (filterNonemptyGates_pairwise _ L.disjoint)
        (fun G hG => ((mem_filterNonemptyGates G L.gates).mp hG).2)
    _ ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

private theorem pairwise_append_identityGates (gates : List (ListGate n dim q))
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support)) (k : ℕ) :
    (gates ++ List.replicate k (identityListGate : ListGate n dim q)).Pairwise
      (fun (G H : ListGate n dim q) => Disjoint G.support H.support) := by
  revert hpair
  induction gates with
  | nil =>
      intro hpair
      induction k with
      | zero => simp
      | succ k ih =>
          simp only [List.nil_append, List.replicate_succ, List.pairwise_cons] at *
          exact ⟨fun H _ => by simp [identityListGate], ih⟩
  | cons G gates ih =>
      intro hpair
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      rw [List.cons_append, List.pairwise_cons]
      refine ⟨?_, ih htail⟩
      intro H hH
      rcases List.mem_append.mp hH with hH | hH
      · exact hhead H hH
      · have heq : H = (identityListGate : ListGate n dim q) := by
          simp only [List.mem_replicate] at hH
          aesop
        subst H
        simp [identityListGate]

private theorem gateList_get_disjoint (gates : List (ListGate n dim q))
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support))
    (i j : ℕ) (hi : i < gates.length) (hj : j < gates.length) (hij : i ≠ j) :
    Disjoint (gates[i]'hi).support (gates[j]'hj).support := by
  have hget := List.pairwise_iff_getElem.mp hpair
  by_cases hlt : i < j
  · exact hget i j hi hj hlt
  · have hgt : j < i := by omega
    exact (hget j i hj hi hgt).symm

def layerOfGateList (gates : List (ListGate n dim q)) (hlen : gates.length = n)
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support)) : Layer n dim q where
  support i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).support
  gate i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).gate
  disjoint := by
    intro i j hij
    apply gateList_get_disjoint gates hpair i.val j.val
      (by simpa only [hlen] using i.isLt) (by simpa only [hlen] using j.isLt)
    intro heq
    apply hij
    exact Fin.ext heq
  arity i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).arity
  locality i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).locality
  unitary i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).unitary

theorem layerOfGateList_eval (gates : List (ListGate n dim q)) (hlen : gates.length = n)
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support)) :
    (layerOfGateList gates hlen hpair).eval = listGateEval gates := by
  have hlist : List.ofFn (layerOfGateList gates hlen hpair).gate = gates.map ListGate.gate := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, layerOfGateList]
  unfold Layer.eval listGateEval
  rw [hlist]

def ArbitraryLayer.normalized (L : ArbitraryLayer n dim q) : Layer n dim q :=
  layerOfGateList
    (filterNonemptyGates L.gates ++
      List.replicate (n - (filterNonemptyGates L.gates).length) identityListGate)
    (by
      simp only [List.length_append, List.length_replicate]
      have h := filterNonemptyGates_length_le L
      omega)
    (pairwise_append_identityGates _ (filterNonemptyGates_pairwise _ L.disjoint) _)

theorem ArbitraryLayer.normalized_eval (L : ArbitraryLayer n dim q) :
    L.normalized.eval = listGateEval (filterNonemptyGates L.gates) := by
  rw [ArbitraryLayer.normalized, layerOfGateList_eval]
  simp [listGateEval, List.map_append, List.reverse_append, List.prod_append, identityListGate]

theorem scalar_of_supportedOn_empty {U : Operator (PhysicalBasis n dim)}
    (hsupported : SupportedOn U ∅) : IsScalar U := by
  obtain ⟨A, rfl⟩ := hsupported
  have no_mem (j : Fin n) : j ∉ (∅ : Finset (Fin n)) := by simp
  let e : LocalBasis dim (∅ : Finset (Fin n)) :=
    fun i => False.elim (no_mem i.1 i.2)
  have hA : A = A e e • (1 : Operator (LocalBasis dim (∅ : Finset (Fin n)))) := by
    ext x y
    have hx : x = e := by
      funext i
      exact False.elim (no_mem i.1 i.2)
    have hy : y = e := by
      funext i
      exact False.elim (no_mem i.1 i.2)
    subst x
    subst y
    simp
  refine ⟨A e e, ?_⟩
  calc
    localEmbed ∅ A = localEmbed ∅ (A e e • (1 : Operator (LocalBasis dim ∅))) :=
      congrArg (localEmbed ∅) hA
    _ = A e e • (1 : Operator (PhysicalBasis n dim)) := by
      rw [localEmbed_smul, localEmbed_one]

private theorem normalization_phase_mul {a b : ℂ}
    (ha : star a * a = 1) (hb : star b * b = 1) : star (a * b) * (a * b) = 1 := by
  calc
    star (a * b) * (a * b) = (star a * a) * (star b * b) := by rw [star_mul]; ring
    _ = 1 := by rw [ha, hb, mul_one]

theorem listGateEval_filter_phase [Nonempty (PhysicalBasis n dim)]
    (gates : List (ListGate n dim q)) :
    ProjectivelyEquivalent (listGateEval gates) (listGateEval (filterNonemptyGates gates)) := by
  induction gates with
  | nil => exact projectivelyEquivalent_refl 1
  | cons G gates ih =>
      obtain ⟨z, hz, heval⟩ := ih
      by_cases hG : G.support = ∅
      · have hscalar : IsScalar G.gate := scalar_of_supportedOn_empty (by simpa [hG] using G.locality)
        obtain ⟨c, hc, hgate⟩ := projectivelyEquivalent_one_of_unitary_scalar G.unitary hscalar
        refine ⟨c * z, normalization_phase_mul hc hz, ?_⟩
        simp only [listGateEval_cons, filterNonemptyGates, if_pos hG, heval, hgate,
          smul_mul_assoc, mul_smul_comm, smul_smul, mul_one]
      · refine ⟨z, hz, ?_⟩
        simp only [listGateEval_cons, filterNonemptyGates, if_neg hG, heval, smul_mul_assoc]

theorem ArbitraryLayer.normalization_phase [Nonempty (PhysicalBasis n dim)]
    (L : ArbitraryLayer n dim q) : ProjectivelyEquivalent L.eval L.normalized.eval := by
  rw [L.normalized_eval]
  exact listGateEval_filter_phase L.gates

theorem code_physicalBasis_nonempty {K g : ℕ} (C : Code n dim K g)
    (hK : 2 ≤ K) (hg : 1 ≤ g) : Nonempty (PhysicalBasis n dim) := by
  by_contra h
  letI : IsEmpty (PhysicalBasis n dim) := ⟨fun x => h ⟨x⟩⟩
  let j : Fin K × Fin g := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hdiag := congrArg (fun A : Operator (Fin K × Fin g) => A j j) C.isometry
  simp [Matrix.mul_apply] at hdiag

abbrev ArbitraryCircuit (n : ℕ) (dim : Fin n → ℕ) (q h : ℕ) :=
  Fin h → ArbitraryLayer n dim q

def arbitraryCircuitEval {h : ℕ} (c : ArbitraryCircuit n dim q h) :
    Operator (PhysicalBasis n dim) := (List.ofFn fun i => (c i).eval).reverse.prod

def ArbitraryCircuit.normalized {h : ℕ} (c : ArbitraryCircuit n dim q h) :
    Circuit n dim q h := fun i => (c i).normalized

private theorem normalization_projective_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A A' B B' : Operator ι}
    (hA : ProjectivelyEquivalent A A') (hB : ProjectivelyEquivalent B B') :
    ProjectivelyEquivalent (A * B) (A' * B') := by
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  refine ⟨b * a, normalization_phase_mul hb ha, ?_⟩
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]

private theorem normalization_projective_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] (pairs : List (Operator ι × Operator ι))
    (h : ∀ p ∈ pairs, ProjectivelyEquivalent p.1 p.2) :
    ProjectivelyEquivalent (pairs.map Prod.fst).prod (pairs.map Prod.snd).prod := by
  revert h
  induction pairs with
  | nil =>
      intro h
      exact projectivelyEquivalent_refl 1
  | cons p pairs ih =>
      intro h
      have hp := h p (by simp)
      have htail : ∀ r ∈ pairs, ProjectivelyEquivalent r.1 r.2 := by
        intro r hr
        exact h r (by simp [hr])
      simpa only [List.map_cons, List.prod_cons] using normalization_projective_mul hp (ih htail)

theorem arbitraryCircuit_normalization_phase [Nonempty (PhysicalBasis n dim)]
    {h : ℕ} (c : ArbitraryCircuit n dim q h) :
    ProjectivelyEquivalent (arbitraryCircuitEval c) (circuitEval c.normalized) := by
  let pairs := (List.ofFn fun i => ((c i).eval, (c i).normalized.eval)).reverse
  have hp : ∀ p ∈ pairs, ProjectivelyEquivalent p.1 p.2 := by
    intro p hp
    have hp' : ∃ i, ((c i).eval, (c i).normalized.eval) = p := by
      simpa only [pairs, List.mem_reverse, List.mem_ofFn] using hp
    obtain ⟨i, rfl⟩ := hp'
    exact (c i).normalization_phase
  have hh := normalization_projective_prod pairs hp
  simpa [pairs, arbitraryCircuitEval, circuitEval, ArbitraryCircuit.normalized,
    List.map_reverse, List.map_ofFn, Function.comp_def] using hh

private theorem normalization_rect_smul_mul {α β γ : Type*} [Fintype β]
    (a : ℂ) (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    (a • A) * B = a • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

private theorem normalization_rect_mul_smul {α β γ : Type*} [Fintype β]
    (a : ℂ) (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    A * (a • B) = a • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm, mul_assoc]

private theorem normalization_unitary_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℂ) {U : Operator ι}
    (ha : star a * a = 1) (hU : IsUnitary U) : IsUnitary (a • U) := by
  have ha' : a * star a = 1 := by simpa only [mul_comm] using ha
  constructor
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.1]
    change (a * star a) • (1 : Operator ι) = 1
    rw [ha', one_smul]
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.2]
    change (star a * a) • (1 : Operator ι) = 1
    rw [ha, one_smul]

theorem implements_of_projectivelyEquivalent_physical {K g : ℕ}
    (C : Code n dim K g) {U V : Operator (PhysicalBasis n dim)} {W : Operator (Fin K)}
    (hphase : ProjectivelyEquivalent U V) (himpl : Implements C U W) : Implements C V W := by
  obtain ⟨a, ha, hUV⟩ := hphase
  obtain ⟨hW, Z, hZ, hencoded⟩ := himpl
  have ha' : a * star a = 1 := by simpa only [mul_comm] using ha
  have hstar : star (star a) * star a = 1 := by simpa only [star_star] using ha'
  refine ⟨hW, star a • Z, normalization_unitary_smul _ hstar hZ, ?_⟩
  have hk : W ⊗ₖ (star a • Z) = star a • (W ⊗ₖ Z) := by
    ext ⟨i, s⟩ ⟨j, t⟩
    simp [Matrix.kronecker_apply, smul_eq_mul, mul_left_comm]
  calc
    V * C.encoding = (star a * a) • (V * C.encoding) := by rw [ha, one_smul]
    _ = star a • (U * C.encoding) := by
      rw [hUV, normalization_rect_smul_mul, smul_smul]
    _ = star a • (C.encoding * (W ⊗ₖ Z)) := by rw [hencoded]
    _ = C.encoding * (W ⊗ₖ (star a • Z)) := by
      rw [hk, normalization_rect_mul_smul]

def arbitraryLogicalImage {K g : ℕ} (C : Code n dim K g) (q h : ℕ) :
    Set (ProjectiveOperator (Fin K)) :=
  {a | ∃ c : ArbitraryCircuit n dim q h, ∃ W : Operator (Fin K),
    Implements C (arbitraryCircuitEval c) W ∧ projectiveClass W = a}

theorem arbitraryLogicalImage_subset_logicalImage {K g h : ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g) :
    arbitraryLogicalImage C q h ⊆ logicalImage C q h := by
  letI : Nonempty (PhysicalBasis n dim) := code_physicalBasis_nonempty C hK hg
  rintro a ⟨c, W, himpl, hclass⟩
  exact ⟨c.normalized, W,
    implements_of_projectivelyEquivalent_physical C (arbitraryCircuit_normalization_phase c) himpl,
    hclass⟩

def Layer.toArbitrary (L : Layer n dim q) : ArbitraryLayer n dim q where
  gates := List.ofFn fun i =>
    { support := L.support i, gate := L.gate i, arity := L.arity i,
      locality := L.locality i, unitary := L.unitary i }
  disjoint := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn]
    apply L.disjoint ⟨i, hi⟩ ⟨j, hj⟩
    intro heq
    have hv : i = j := congrArg Fin.val heq
    omega

@[simp] theorem Layer.toArbitrary_eval (L : Layer n dim q) : L.toArbitrary.eval = L.eval := by
  simp [ArbitraryLayer.eval, Layer.toArbitrary, listGateEval, Layer.eval, List.map_ofFn,
    Function.comp_def]

theorem logicalImage_subset_arbitraryLogicalImage {K g h : ℕ} (C : Code n dim K g) :
    logicalImage C q h ⊆ arbitraryLogicalImage C q h := by
  rintro a ⟨c, W, himpl, hclass⟩
  refine ⟨fun i => (c i).toArbitrary, W, ?_, hclass⟩
  simpa only [arbitraryCircuitEval, circuitEval, Layer.toArbitrary_eval] using himpl

/-- The finite-list and bounded-slot models have exactly the same logical image. -/
theorem arbitraryLogicalImage_eq_logicalImage {K g h : ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g) :
    arbitraryLogicalImage C q h = logicalImage C q h := by
  exact Set.Subset.antisymm (arbitraryLogicalImage_subset_logicalImage C hK hg)
    (logicalImage_subset_arbitraryLogicalImage C)

theorem arbitraryLogicalImage_finite_of_logicalImage_finite {K g h : ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g)
    (hfinite : (logicalImage C q h).Finite) : (arbitraryLogicalImage C q h).Finite := by
  rw [arbitraryLogicalImage_eq_logicalImage C hK hg]
  exact hfinite

end CriticalDepth.Manuscript
