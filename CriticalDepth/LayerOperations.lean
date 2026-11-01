import CriticalDepth.Support

/-!
# Operations on actual full-register layers

Layer inversion reverses the gate slots before taking adjoints. It therefore
does not assume an unproved permutation law for the layer product. The
single-gate constructor keeps the same physical register and uses identity
gates on empty supports in every other slot.
-/

noncomputable section

namespace CriticalDepth

open Matrix

theorem isUnitary_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsUnitary (1 : Operator ι) := by
  constructor <;> simp

theorem isUnitary_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Operator ι} (hU : IsUnitary U) : IsUnitary (star U) := by
  constructor
  · simpa only [star_star] using hU.2
  · simpa only [star_star] using hU.1

theorem isUnitary_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Operator ι} (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  constructor
  · calc
      star (U * V) * (U * V) = star V * (star U * U) * V := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hU.1, mul_one, hV.1]
  · calc
      (U * V) * star (U * V) = U * (V * star V) * star U := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hV.2, mul_one, hU.2]

theorem matrixList_prod_isUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] (gates : List (Operator ι))
    (hgate : ∀ U ∈ gates, IsUnitary U) : IsUnitary gates.prod := by
  revert hgate
  induction gates with
  | nil =>
      intro hgate
      exact isUnitary_one
  | cons U gates ih =>
      intro hgate
      have hU := hgate U (by simp)
      have hg : ∀ V ∈ gates, IsUnitary V := by
        intro V hV
        exact hgate V (by simp [hV])
      exact isUnitary_mul hU (ih hg)

theorem star_matrixList_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] (gates : List (Operator ι)) :
    star gates.prod = (gates.reverse.map star).prod := by
  induction gates with
  | nil => simp
  | cons U gates ih =>
      simp [List.prod_cons, star_mul, ih, List.reverse_cons, List.map_append, List.prod_append]

private theorem reverse_ofFn_slots {α : Type*} {m : ℕ} (f : Fin m → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
  apply congrArg f
  apply Fin.ext
  simp [Fin.rev] <;> omega

namespace Manuscript

variable {n q : ℕ} {dim : Fin n → ℕ}

def Layer.adjoint (L : Layer n dim q) : Layer n dim q where
  support i := L.support i.rev
  gate i := star (L.gate i.rev)
  disjoint := by
    intro i j hij
    apply L.disjoint
    intro h
    apply hij
    have hh := congrArg Fin.rev h
    simpa only [Fin.rev_rev] using hh
  arity i := L.arity i.rev
  locality i := by
    change SupportedOn (L.gate i.rev).conjTranspose (L.support i.rev)
    exact (L.locality i.rev).conjTranspose
  unitary i := isUnitary_star (L.unitary i.rev)

theorem Layer.evalIsUnitary (L : Layer n dim q) : IsUnitary L.eval := by
  apply matrixList_prod_isUnitary
  intro U hU
  have hU' : ∃ i, L.gate i = U := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hU
  obtain ⟨i, rfl⟩ := hU'
  exact L.unitary i

theorem Layer.eval_adjoint (L : Layer n dim q) : L.adjoint.eval = star L.eval := by
  simp [Layer.eval, Layer.adjoint, reverse_ofFn_slots, List.map_ofFn,
    star_matrixList_prod, Fin.rev_rev, Function.comp_def]

theorem layerSequenceEval_isUnitary (layers : List (Layer n dim q)) :
    IsUnitary (layerSequenceEval layers) := by
  induction layers with
  | nil => exact isUnitary_one
  | cons L layers ih =>
      exact isUnitary_mul ih L.evalIsUnitary

theorem layerSequenceEval_append (first second : List (Layer n dim q)) :
    layerSequenceEval (first ++ second) =
      layerSequenceEval second * layerSequenceEval first := by
  induction first with
  | nil => simp [layerSequenceEval]
  | cons L first ih => simp [layerSequenceEval, ih, mul_assoc]

theorem layerSequenceEval_reverse_adjoint (layers : List (Layer n dim q)) :
    layerSequenceEval (layers.reverse.map Layer.adjoint) = star (layerSequenceEval layers) := by
  induction layers with
  | nil => simp [layerSequenceEval]
  | cons L layers ih =>
      have ih' : layerSequenceEval (layers.map Layer.adjoint).reverse =
          star (layerSequenceEval layers) := by
        simpa only [List.map_reverse] using ih
      simp [List.reverse_cons, List.map_append, layerSequenceEval_append,
        layerSequenceEval, Layer.eval_adjoint, ih', star_mul]

def singleGateLayer (hn : 0 < n) (S : Finset (Fin n))
    (U : Operator (PhysicalBasis n dim)) (hS : S.card ≤ q)
    (hsupported : SupportedOn U S) (hunitary : IsUnitary U) : Layer n dim q where
  support i := if i.val = 0 then S else ∅
  gate i := if i.val = 0 then U else 1
  disjoint := by
    intro i j hij
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · exact False.elim (hij (Fin.ext (hi.trans hj.symm)))
      · simp [hi, hj]
    · simp [hi]
  arity i := by
    by_cases hi : i.val = 0
    · simpa [hi] using hS
    · simp [hi]
  locality i := by
    by_cases hi : i.val = 0
    · simpa [hi] using hsupported
    · simpa [hi] using supportedOn_one (dim := dim) (∅ : Finset (Fin n))
  unitary i := by
    by_cases hi : i.val = 0
    · simpa [hi] using hunitary
    · simpa [hi] using (isUnitary_one (ι := PhysicalBasis n dim))

theorem singleGateLayer_eval (hn : 0 < n) (S : Finset (Fin n))
    (U : Operator (PhysicalBasis n dim)) (hS : S.card ≤ q)
    (hsupported : SupportedOn U S) (hunitary : IsUnitary U) :
    (singleGateLayer hn S U hS hsupported hunitary).eval = U := by
  cases n with
  | zero => omega
  | succ m =>
      simp [Layer.eval, singleGateLayer, List.ofFn_succ, List.reverse_cons, List.prod_append]

end Manuscript
end CriticalDepth
