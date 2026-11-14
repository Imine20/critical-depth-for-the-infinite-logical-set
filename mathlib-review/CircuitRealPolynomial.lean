import CriticalDepthMathlib
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
Real polynomial equations for unitary circuit witnesses with a prescribed layout.
The algebra of pairs of real polynomials is the quadratic algebra for i² = -1.
-/

noncomputable section

namespace CriticalDepth.CircuitRealPolynomial

open CriticalDepth.Manuscript CriticalDepth.Manuscript.ReviewBridges CriticalDepth.ReviewV2
open scoped Kronecker

abbrev RealPoly (σ : Type*) := MvPolynomial σ ℝ

abbrev ComplexPoly (σ : Type*) := QuadraticAlgebra (RealPoly σ) (-1) 0

def evaluation {σ : Type*} (x : σ → ℝ) : ComplexPoly σ →+* ℂ where
  toFun z := ⟨MvPolynomial.eval x z.re, MvPolynomial.eval x z.im⟩
  map_zero' := by apply Complex.ext <;> simp
  map_one' := by apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by apply Complex.ext <;> simp
  map_mul' z w := by
    apply Complex.ext
    · simp [Complex.mul_re, QuadraticAlgebra.re_mul, sub_eq_add_neg]
    · simp [Complex.mul_im, QuadraticAlgebra.im_mul]

@[simp] theorem evaluation_re {σ : Type*} (x : σ → ℝ) (z : ComplexPoly σ) :
    (evaluation x z).re = MvPolynomial.eval x z.re := rfl

@[simp] theorem evaluation_im {σ : Type*} (x : σ → ℝ) (z : ComplexPoly σ) :
    (evaluation x z).im = MvPolynomial.eval x z.im := rfl

def constant {σ : Type*} (z : ℂ) : ComplexPoly σ :=
  ⟨MvPolynomial.C z.re, MvPolynomial.C z.im⟩

@[simp] theorem evaluation_constant {σ : Type*} (x : σ → ℝ) (z : ℂ) :
    evaluation x (constant z) = z := by
  apply Complex.ext <;> simp [constant]

@[simp] theorem evaluation_star {σ : Type*} (x : σ → ℝ) (z : ComplexPoly σ) :
    evaluation x (star z) = star (evaluation x z) := by
  apply Complex.ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

def polyVariable {σ : Type*} (i : σ) : ComplexPoly (σ × Bool) :=
  ⟨MvPolynomial.X (i, false), MvPolynomial.X (i, true)⟩

@[simp] theorem evaluation_variable {σ : Type*} (x : σ × Bool → ℝ) (i : σ) :
    evaluation x (polyVariable i) = ⟨x (i, false), x (i, true)⟩ := by
  apply Complex.ext <;> simp [polyVariable]

theorem map_mul {σ I J K : Type*} [Fintype J] (x : σ → ℝ)
    (A : Matrix I J (ComplexPoly σ)) (B : Matrix J K (ComplexPoly σ)) :
    (A * B).map (evaluation x) = A.map (evaluation x) * B.map (evaluation x) := by
  exact Matrix.map_mul

theorem map_conjTranspose {σ I J : Type*} (x : σ → ℝ)
    (A : Matrix I J (ComplexPoly σ)) :
    A.conjTranspose.map (evaluation x) = (A.map (evaluation x)).conjTranspose := by
  ext i j
  exact evaluation_star x (A j i)

theorem map_kronecker {σ I J K L : Type*} (x : σ → ℝ)
    (A : Matrix I J (ComplexPoly σ)) (B : Matrix K L (ComplexPoly σ)) :
    (A ⊗ₖ B).map (evaluation x) = A.map (evaluation x) ⊗ₖ B.map (evaluation x) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  exact (evaluation x).map_mul (A i j) (B k l)

def entries {σ I J : Type*} (A B : Matrix I J (ComplexPoly σ)) : Set (RealPoly σ) :=
  (Set.range fun i : I × J => (A i.1 i.2 - B i.1 i.2).re) ∪
  (Set.range fun i : I × J => (A i.1 i.2 - B i.1 i.2).im)

theorem entries_zero_iff {σ I J : Type*} (x : σ → ℝ)
    (A B : Matrix I J (ComplexPoly σ)) :
    (∀ f ∈ entries A B, MvPolynomial.eval x f = 0) ↔
      A.map (evaluation x) = B.map (evaluation x) := by
  constructor
  · intro h
    ext i j
    have hr := h _ (Or.inl ⟨(i, j), rfl⟩)
    have hi := h _ (Or.inr ⟨(i, j), rfl⟩)
    have hz : evaluation x (A i j - B i j) = 0 :=
      Complex.ext hr hi
    rw [(evaluation x).map_sub, sub_eq_zero] at hz
    exact hz
  · intro h f hf
    have zero (i : I × J) : evaluation x (A i.1 i.2 - B i.1 i.2) = 0 := by
      rw [(evaluation x).map_sub, sub_eq_zero]
      exact congrFun (congrFun h i.1) i.2
    rcases hf with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact congrArg Complex.re (zero i)
    · exact congrArg Complex.im (zero i)

variable {n r K g : ℕ} {dim : Fin n → ℕ}
    (support : GateIndex n r → Finset (Fin n))

abbrev EntryIndex (K g : ℕ) :=
  (Σ p : GateIndex n r, LocalBasis dim (support p) × LocalBasis dim (support p)) ⊕
    ((Fin K × Fin K) ⊕ (Fin g × Fin g))

abbrev Variables (K g : ℕ) := EntryIndex (dim := dim) support K g × Bool

def gate (p : GateIndex n r) :
    Matrix (LocalBasis dim (support p)) (LocalBasis dim (support p))
      (ComplexPoly (Variables (dim := dim) support K g)) :=
  fun i j => polyVariable (Sum.inl ⟨p, i, j⟩)

def logical : Matrix (Fin K) (Fin K) (ComplexPoly (Variables (dim := dim) support K g)) :=
  fun i j => polyVariable (Sum.inr (Sum.inl (i, j)))

def gauge : Matrix (Fin g) (Fin g) (ComplexPoly (Variables (dim := dim) support K g)) :=
  fun i j => polyVariable (Sum.inr (Sum.inr (i, j)))

def embed {σ : Type*} (S : Finset (Fin n))
    (A : Matrix (LocalBasis dim S) (LocalBasis dim S) (ComplexPoly σ)) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) (ComplexPoly σ) := by
  classical
  exact fun i j =>
    if ∀ l, l ∉ S → i l = j l then A (fun l => i l.val) (fun l => j l.val) else 0

theorem map_embed {σ : Type*} (x : σ → ℝ) (S : Finset (Fin n))
    (A : Matrix (LocalBasis dim S) (LocalBasis dim S) (ComplexPoly σ)) :
    (embed S A).map (evaluation x) = localEmbed S (A.map (evaluation x)) := by
  classical
  ext i j
  simp only [embed, localEmbed, Matrix.map_apply]
  split <;> simp_all

def total : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim)
    (ComplexPoly (Variables (dim := dim) support K g)) :=
  (List.ofFn fun i : Fin r =>
    (List.ofFn fun j : Fin n => embed (support (i, j)) (gate (dim := dim) support (i, j))).reverse.prod
    ).reverse.prod

def unitaryRelations {σ I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ComplexPoly σ)) : Set (RealPoly σ) :=
  entries (A.conjTranspose * A) 1 ∪ entries (A * A.conjTranspose) 1

theorem unitaryRelations_zero_iff {σ I : Type*} [Fintype I] [DecidableEq I]
    (x : σ → ℝ) (A : Matrix I I (ComplexPoly σ)) :
    (∀ f ∈ unitaryRelations A, MvPolynomial.eval x f = 0) ↔
      IsUnitary (A.map (evaluation x)) := by
  classical
  have ho : (1 : Matrix I I (ComplexPoly σ)).map (evaluation x) = 1 :=
    Matrix.map_one _ (evaluation x).map_zero (evaluation x).map_one
  rw [unitaryRelations, Set.forall_mem_union, entries_zero_iff, entries_zero_iff,
    map_mul, map_mul, map_conjTranspose, ho]
  rfl

def relations (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) :
    Set (RealPoly (Variables (dim := dim) support K g)) :=
  (⋃ p : GateIndex n r, unitaryRelations (gate (dim := dim) support p)) ∪
    (unitaryRelations (logical (dim := dim) support) ∪ (unitaryRelations (gauge (dim := dim) support) ∪
      entries (total (dim := dim) support * V.map constant)
        (V.map constant * (logical (dim := dim) support ⊗ₖ gauge (dim := dim) support))))

def witnessIdeal (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) :
    Ideal (RealPoly (Variables (dim := dim) support K g)) :=
  Ideal.span (relations support V)

theorem witnessIdeal_zero_iff (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (x : Variables (dim := dim) support K g → ℝ) :
    (∀ f ∈ witnessIdeal support V, MvPolynomial.eval x f = 0) ↔
      (∀ p, IsUnitary ((gate (dim := dim) support p).map (evaluation x))) ∧
      IsUnitary ((logical (dim := dim) support).map (evaluation x)) ∧
      IsUnitary ((gauge (dim := dim) support).map (evaluation x)) ∧
      (total (dim := dim) support).map (evaluation x) * V =
        V * (((logical (dim := dim) support).map (evaluation x)) ⊗ₖ
              ((gauge (dim := dim) support).map (evaluation x))) := by
  have hspan : (∀ f ∈ witnessIdeal support V, MvPolynomial.eval x f = 0) ↔
      ∀ f ∈ relations support V, MvPolynomial.eval x f = 0 := by
    change (Ideal.span _ ≤ RingHom.ker (MvPolynomial.eval x)) ↔
      (_ ⊆ (RingHom.ker (MvPolynomial.eval x) : Set (RealPoly (Variables (dim := dim) support K g))))
    exact Ideal.span_le
  have hV : (V.map (constant (σ := Variables (dim := dim) support K g))).map (evaluation x) = V := by
    ext i j
    exact evaluation_constant x (V i j)
  simp only [hspan, relations, Set.forall_mem_union, unitaryRelations_zero_iff,
    entries_zero_iff, map_mul, map_kronecker, hV, Set.mem_iUnion, forall_exists_index]
  apply and_congr_left
  intro _
  constructor
  · intro H p
    exact (unitaryRelations_zero_iff x _).mp fun f hf => H f p hf
  · intro H f p hp
    exact (unitaryRelations_zero_iff x _).mpr (H p) f hp


/-- Entrywise evaluation commutes with the chronological product. -/
theorem map_total (x : Variables (dim := dim) support K g → ℝ) :
    (total (dim := dim) support).map (evaluation x) =
      (List.ofFn fun i : Fin r =>
        (List.ofFn fun j : Fin n =>
          localEmbed (support (i,j)) ((gate (dim := dim) support (i,j)).map (evaluation x))).reverse.prod
      ).reverse.prod := by
  classical
  let ψ := (evaluation x).mapMatrix (m := PhysicalBasis n dim)
  change ψ (total (dim := dim) support) = _
  unfold total
  rw [map_list_prod, List.map_reverse, List.map_ofFn]
  congr 2
  apply congrArg List.ofFn
  funext i
  change ψ ((List.ofFn fun j : Fin n =>
    embed (support (i,j)) (gate (dim := dim) support (i,j))).reverse.prod) = _
  rw [map_list_prod, List.map_reverse, List.map_ofFn]
  congr 2
  apply congrArg List.ofFn
  funext j
  exact map_embed x _ _

def admissible (q : ℕ) : Prop :=
  (∀ p, (support p).card ≤ q) ∧
  ∀ i j k, j ≠ k → Disjoint (support (i,j)) (support (i,k))

def toCircuit (x : Variables (dim := dim) support K g → ℝ) (q : ℕ)
    (hs : admissible support q)
    (hu : ∀ p, IsUnitary ((gate (dim := dim) support p).map (evaluation x))) :
    Circuit n dim q r := fun i =>
  { support := fun j => support (i,j)
    gate := fun j => localEmbed _ ((gate (dim := dim) support (i,j)).map (evaluation x))
    disjoint := hs.2 i
    arity := fun j => hs.1 (i,j)
    locality := fun _ => ⟨_, rfl⟩
    unitary := fun j => localEmbed_isUnitary _ _ (hu (i,j)) }

theorem toCircuit_eval (x : Variables (dim := dim) support K g → ℝ) (q : ℕ)
    (hs : admissible support q)
    (hu : ∀ p, IsUnitary ((gate (dim := dim) support p).map (evaluation x))) :
    circuitEval (toCircuit support x q hs hu) = (total (dim := dim) support).map (evaluation x) := by
  rw [map_total]
  rfl

def observable (a b : Fin K × Fin K) :
    ComplexPoly (Variables (dim := dim) support K g) :=
  logical (dim := dim) (g := g) support a.1 b.1 * star (logical (dim := dim) (g := g) support a.2 b.2)

theorem evaluation_observable (x : Variables (dim := dim) support K g → ℝ) (a b : Fin K × Fin K) :
    evaluation x (observable (dim := dim) (g := g) support a b) =
      conjugationCoordinates ((logical (dim := dim) support).map (evaluation x)) a b := by
  simp [observable, conjugationCoordinates, Matrix.map_apply]

/-- The encoding equation at each real witness gives an actual projective
logical gate at the prescribed budget. -/
theorem witness_gate_mem (C : Code n dim K g) (q h : ℕ) (hr : r ≤ h)
    (hs : admissible support q) (x : Variables (dim := dim) support K g → ℝ)
    (hx : ∀ f ∈ witnessIdeal support C.encoding, MvPolynomial.eval x f = 0) :
    ∃ W : Matrix.unitaryGroup (Fin K) ℂ,
      W.val = (logical (dim := dim) support).map (evaluation x) ∧
      CriticalDepth.ReviewV2.projectiveMk (ι := Fin K) W ∈
        CriticalDepth.ReviewV2.nativeLogicalImage C.encoding q h := by
  have ⟨hU, hW, hZ, he⟩ := (witnessIdeal_zero_iff support C.encoding x).mp hx
  let W : Matrix.unitaryGroup (Fin K) ℂ :=
    ⟨_, (isUnitary_iff_mem_unitaryGroup _ _).mp hW⟩
  refine ⟨W, rfl, ?_⟩
  rw [nativeLogicalImage_eq_preimage _ C.isometry]
  apply Set.mem_preimage.mpr
  rw [puToProjectiveOperator_mk]
  apply logicalImage_subset_atMost C q r h hr
  refine ⟨toCircuit support x q hs hU, W.val, ⟨hW, _, hZ, ?_⟩, rfl⟩
  rwa [toCircuit_eval]

def encodePoint (A : ∀ p, Matrix (LocalBasis dim (support p)) (LocalBasis dim (support p)) ℂ)
    (W : Matrix (Fin K) (Fin K) ℂ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    Variables (dim := dim) support K g → ℝ := fun (v, part) =>
  let z := match v with
    | .inl ⟨p, i, j⟩ => A p i j
    | .inr (.inl (i,j)) => W i j
    | .inr (.inr (i,j)) => Z i j
  if part then z.im else z.re

private theorem point_gate
    (A : ∀ p, Matrix (LocalBasis dim (support p)) (LocalBasis dim (support p)) ℂ)
    (W : Matrix (Fin K) (Fin K) ℂ) (Z : Matrix (Fin g) (Fin g) ℂ) (p : GateIndex n r) :
    (gate (dim := dim) support p).map (evaluation (encodePoint support A W Z)) = A p := by
  ext i j
  simp [gate, encodePoint, Matrix.map_apply, Complex.eta]

private theorem point_logical
    (A : ∀ p, Matrix (LocalBasis dim (support p)) (LocalBasis dim (support p)) ℂ)
    (W : Matrix (Fin K) (Fin K) ℂ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    (logical (dim := dim) support).map (evaluation (encodePoint support A W Z)) = W := by
  ext i j
  simp [logical, encodePoint, Matrix.map_apply, Complex.eta]

private theorem point_gauge
    (A : ∀ p, Matrix (LocalBasis dim (support p)) (LocalBasis dim (support p)) ℂ)
    (W : Matrix (Fin K) (Fin K) ℂ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    (gauge (dim := dim) support).map (evaluation (encodePoint support A W Z)) = Z := by
  ext i j
  simp [gauge, encodePoint, Matrix.map_apply, Complex.eta]

theorem point_of_implements (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g)
    (q : ℕ) (L : Circuit n dim q r) (W : Operator (Fin K))
    (hW : Implements C (circuitEval L) W) :
    ∃ x : Variables (dim := dim) (layoutSupport L) K g → ℝ,
      (∀ f ∈ witnessIdeal (layoutSupport L) C.encoding, MvPolynomial.eval x f = 0) ∧
      (logical (dim := dim) (layoutSupport L)).map (evaluation x) = W := by
  classical
  obtain ⟨hWu, Z, hZu, henc⟩ := hW
  have hlocal (p : GateIndex n r) :
      ∃ A : Matrix (LocalBasis dim (layoutSupport L p)) (LocalBasis dim (layoutSupport L p)) ℂ,
        (L p.1).gate p.2 = localEmbed (layoutSupport L p) A := (L p.1).locality p.2
  choose A hA using hlocal
  let x := encodePoint (layoutSupport L) A W Z
  have hGate (p : GateIndex n r) :
      (gate (dim := dim) (layoutSupport L) p).map (evaluation x) = A p :=
    point_gate (layoutSupport L) A W Z p
  have hL := point_logical (layoutSupport L) A W Z
  have hZ := point_gauge (layoutSupport L) A W Z
  refine ⟨x, (witnessIdeal_zero_iff _ _ _).mpr ⟨?_, ?_, ?_, ?_⟩, hL⟩
  · intro p
    rw [hGate p]
    apply (localEmbed_isUnitary_iff_of_code C hK hg (layoutSupport L p) (A p)).mp
    rw [← hA p]
    exact (L p.1).unitary p.2
  · rwa [hL]
  · rwa [hZ]
  · have ht : (total (dim := dim) (layoutSupport L)).map (evaluation x) = circuitEval L := by
      rw [map_total]
      unfold circuitEval Layer.eval
      congr 2
      apply congrArg List.ofFn
      funext i
      congr 2
      apply congrArg List.ofFn
      funext j
      rw [hGate (i,j)]
      exact (hA (i,j)).symm
    rwa [ht, hL, hZ]

/-- At least one admissible depth and layout has infinitely many values of a
single real entry of the conjugation action. -/
theorem infinite_observable_of_infinite_image (C : Code n dim K g)
    (hK : 2 ≤ K) (hg : 1 ≤ g) (q h : ℕ)
    (hi : (CriticalDepth.ReviewV2.nativeLogicalImage C.encoding q h).Infinite) :
    ∃ (r : Fin (h + 1)) (s : GateIndex n r.val → Finset (Fin n)),
      admissible s q ∧ ∃ (a b : Fin K × Fin K) (part : Bool),
        (Set.range fun x : {x : Variables (dim := dim) s K g → ℝ //
            ∀ f ∈ witnessIdeal s C.encoding, MvPolynomial.eval x f = 0} =>
          MvPolynomial.eval x.val
            (if part then (observable (dim := dim) (g := g) s a b).im else (observable (dim := dim) (g := g) s a b).re)
        ).Infinite := by
  classical
  let : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  by_contra hnone
  have hf (r : Fin (h + 1)) (s : GateIndex n r.val → Finset (Fin n))
      (hs : admissible s q) (a b : Fin K × Fin K) (part : Bool) :
      (Set.range fun x : {x : Variables (dim := dim) s K g → ℝ //
          ∀ f ∈ witnessIdeal s C.encoding, MvPolynomial.eval x f = 0} =>
        MvPolynomial.eval x.val
          (if part then (observable (dim := dim) (g := g) s a b).im else (observable (dim := dim) (g := g) s a b).re)
      ).Finite := by
    by_contra hh
    exact hnone ⟨r, s, hs, a, b, part, hh⟩
  let F := fun (r : Fin (h+1)) (s : GateIndex n r.val → Finset (Fin n))
      (x : {x : Variables (dim := dim) s K g → ℝ //
          ∀ f ∈ witnessIdeal s C.encoding, MvPolynomial.eval x f = 0}) =>
    conjugationCoordinates ((logical (dim := dim) s).map (evaluation x.val))
  have finiteFamily (r : Fin (h+1)) (s : GateIndex n r.val → Finset (Fin n)) :
      (if admissible s q then Set.range (F r s) else ∅).Finite := by
    split_ifs with hs
    · let coords := fun x : {x : Variables (dim := dim) s K g → ℝ //
          ∀ f ∈ witnessIdeal s C.encoding, MvPolynomial.eval x f = 0} =>
          fun i : (Fin K × Fin K) × (Fin K × Fin K) × Bool =>
            MvPolynomial.eval x.val
              (if i.2.2 then (observable (dim := dim) (g := g) s i.1 i.2.1).im
                else (observable (dim := dim) (g := g) s i.1 i.2.1).re)
      have hfcoords : (Set.range coords).Finite := by
        apply (Set.Finite.pi fun i => hf r s hs i.1 i.2.1 i.2.2).subset
        rintro y ⟨x, rfl⟩ i _
        exact ⟨x, rfl⟩
      let unflatten : (((Fin K × Fin K) × (Fin K × Fin K) × Bool) → ℝ) →
          Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ :=
        fun v a b => ⟨v (a,b,false), v (a,b,true)⟩
      apply (hfcoords.image unflatten).subset
      rintro y ⟨x, rfl⟩
      refine ⟨coords x, ⟨x, rfl⟩, ?_⟩
      ext a b
      change Complex.mk _ _ = conjugationCoordinates ((logical (dim := dim) s).map (evaluation x.val)) a b
      rw [← evaluation_observable s x.val a b]
      rfl
    · exact Set.finite_empty
  have hFinite : (⋃ (r : Fin (h+1)) (s : GateIndex n r.val → Finset (Fin n)),
      if admissible s q then Set.range (F r s) else ∅).Finite :=
    Set.finite_iUnion fun r => Set.finite_iUnion fun s => finiteFamily r s
  let realW : Set (Operator (Fin K)) :=
    {W | ∃ (r : Fin (h+1)) (L : Circuit n dim q r.val), Implements C (circuitEval L) W}
  have hcoordinates : (conjugationCoordinates '' realW).Finite := hFinite.subset (by
    rintro _ ⟨W, ⟨r, L, hW⟩, rfl⟩
    obtain ⟨x, hx, hl⟩ := point_of_implements C hK hg q L W hW
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨layoutSupport L, ?_⟩⟩
    have hs : admissible (layoutSupport L) q :=
      ⟨fun p => (L p.1).arity p.2, fun i j k hne => (L i).disjoint j k hne⟩
    simp only [hs, if_true]
    exact ⟨⟨x, hx⟩, congrArg conjugationCoordinates hl⟩)
  have hclass : (projectiveClass '' realW).Finite :=
    finite_projectiveImage_of_finite_conjugationCoordinates realW
      (fun W ⟨_, _, hW⟩ => hW.1) hcoordinates
  apply hi
  apply (hclass.preimage (puToProjectiveOperator_injective (ι := Fin K)).injOn).subset
  rw [nativeLogicalImage_eq_preimage _ C.isometry]
  rintro y ⟨depth, hdepth, hy⟩
  rw [arbitraryLogicalImage_eq_logicalImage C hK hg] at hy
  obtain ⟨L, W, hW, hy⟩ := hy
  exact ⟨W, ⟨⟨depth, Nat.lt_succ_of_le hdepth⟩, L, hW⟩, hy⟩
end CriticalDepth.CircuitRealPolynomial
