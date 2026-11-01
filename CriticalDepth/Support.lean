import CriticalDepth.ManuscriptStatements
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Tensor-local support on the full physical register

These lemmas use the manuscript's concrete matrix embedding. No support-growth
law is assumed. In particular, local operators retain the identity on every
site outside the declared support.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

variable {n : ℕ} {dim : Fin n → ℕ}

@[simp] theorem localEmbed_zero (S : Finset (Fin n)) :
    localEmbed S (0 : Operator (LocalBasis dim S)) = 0 := by
  classical
  ext x y
  by_cases h : ∀ i, i ∉ S → x i = y i <;> simp [localEmbed, h]

theorem localEmbed_add (S : Finset (Fin n)) (A B : Operator (LocalBasis dim S)) :
    localEmbed S (A + B) = localEmbed S A + localEmbed S B := by
  classical
  ext x y
  by_cases h : ∀ i, i ∉ S → x i = y i
  · simp only [localEmbed, if_pos h, Matrix.add_apply]
  · simp only [localEmbed, if_neg h, Matrix.add_apply, zero_add]

theorem localEmbed_smul (S : Finset (Fin n)) (z : ℂ)
    (A : Operator (LocalBasis dim S)) :
    localEmbed S (z • A) = z • localEmbed S A := by
  classical
  ext x y
  by_cases h : ∀ i, i ∉ S → x i = y i <;> simp [localEmbed, h]

theorem localEmbed_neg (S : Finset (Fin n)) (A : Operator (LocalBasis dim S)) :
    localEmbed S (-A) = -localEmbed S A := by
  simpa only [neg_one_smul] using localEmbed_smul S (-1 : ℂ) A

theorem localEmbed_sub (S : Finset (Fin n)) (A B : Operator (LocalBasis dim S)) :
    localEmbed S (A - B) = localEmbed S A - localEmbed S B := by
  rw [sub_eq_add_neg, localEmbed_add, localEmbed_neg, sub_eq_add_neg]

def localEmbedLinearMap (S : Finset (Fin n)) :
    Operator (LocalBasis dim S) →ₗ[ℂ] Operator (PhysicalBasis n dim) where
  toFun := localEmbed S
  map_add' := localEmbed_add S
  map_smul' := localEmbed_smul S

@[simp] theorem localEmbed_one (S : Finset (Fin n)) :
    localEmbed S (1 : Operator (LocalBasis dim S)) = 1 := by
  classical
  ext x y
  by_cases hout : ∀ i, i ∉ S → x i = y i
  · by_cases hin : (fun i : S => x i.1) = (fun i : S => y i.1)
    · have hxy : x = y := by
        funext i
        by_cases hi : i ∈ S
        · exact congrFun hin ⟨i, hi⟩
        · exact hout i hi
      subst y
      simp [localEmbed]
    · have hxy : x ≠ y := by
        intro hxy
        apply hin
        rw [hxy]
      simp [localEmbed, hout, Matrix.one_apply, hin, hxy]
  · have hxy : x ≠ y := by
      intro hxy
      apply hout
      intro i hi
      rw [hxy]
    simp [localEmbed, hout, Matrix.one_apply, hxy]

theorem localEmbed_conjTranspose (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) :
    localEmbed S A.conjTranspose = (localEmbed S A).conjTranspose := by
  classical
  ext x y
  by_cases hxy : ∀ i, i ∉ S → x i = y i
  · have hyx : ∀ i, i ∉ S → y i = x i := fun i hi => (hxy i hi).symm
    simp only [Matrix.conjTranspose_apply, localEmbed, if_pos hxy, if_pos hyx]
  · have hyx : ¬ ∀ i, i ∉ S → y i = x i := by
      intro h
      apply hxy
      exact fun i hi => (h i hi).symm
    simp only [Matrix.conjTranspose_apply, localEmbed, if_neg hxy, if_neg hyx, star_zero]

theorem supportedOn_zero (S : Finset (Fin n)) :
    SupportedOn (0 : Operator (PhysicalBasis n dim)) S := by
  exact ⟨0, (localEmbed_zero S).symm⟩

theorem supportedOn_one (S : Finset (Fin n)) :
    SupportedOn (1 : Operator (PhysicalBasis n dim)) S := by
  exact ⟨1, (localEmbed_one S).symm⟩

theorem SupportedOn.add {O P : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P S) :
    SupportedOn (O + P) S := by
  obtain ⟨A, rfl⟩ := hO
  obtain ⟨B, rfl⟩ := hP
  exact ⟨A + B, (localEmbed_add S A B).symm⟩

theorem SupportedOn.smul {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (z : ℂ) :
    SupportedOn (z • O) S := by
  obtain ⟨A, rfl⟩ := hO
  exact ⟨z • A, (localEmbed_smul S z A).symm⟩

theorem SupportedOn.neg {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) : SupportedOn (-O) S := by
  obtain ⟨A, rfl⟩ := hO
  exact ⟨-A, (localEmbed_neg S A).symm⟩

theorem SupportedOn.sub {O P : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P S) :
    SupportedOn (O - P) S := by
  rw [sub_eq_add_neg]
  exact hO.add hP.neg

theorem SupportedOn.conjTranspose {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) :
    SupportedOn O.conjTranspose S := by
  obtain ⟨A, rfl⟩ := hO
  exact ⟨A.conjTranspose, (localEmbed_conjTranspose S A).symm⟩

theorem SupportedOn.affine {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (a b : ℂ) :
    SupportedOn (CriticalDepth.affine O a b) S := by
  exact ((supportedOn_one S).smul a).add (hO.smul b)

theorem supportedOn_univ (O : Operator (PhysicalBasis n dim)) :
    SupportedOn O Finset.univ := by
  classical
  refine ⟨fun x y => O (fun i => x ⟨i, Finset.mem_univ i⟩)
    (fun i => y ⟨i, Finset.mem_univ i⟩), ?_⟩
  ext x y
  simp [localEmbed]

/-- Extend a local matrix to a larger local register by complementary identity. -/
def localInflate (S T : Finset (Fin n)) (hST : S ⊆ T)
    (A : Operator (LocalBasis dim S)) : Operator (LocalBasis dim T) := by
  classical
  exact fun x y =>
    if ∀ i : T, i.1 ∉ S → x i = y i then
      A (fun i => x ⟨i.1, hST i.2⟩) (fun i => y ⟨i.1, hST i.2⟩)
    else 0

theorem localEmbed_localInflate (S T : Finset (Fin n)) (hST : S ⊆ T)
    (A : Operator (LocalBasis dim S)) :
    localEmbed T (localInflate S T hST A) = localEmbed S A := by
  classical
  ext x y
  by_cases hS : ∀ i, i ∉ S → x i = y i
  · have hT : ∀ i, i ∉ T → x i = y i := by
      intro i hi
      apply hS i
      exact fun hiS => hi (hST hiS)
    have hin : ∀ i : T, i.1 ∉ S → x i.1 = y i.1 := by
      intro i hi
      exact hS i.1 hi
    unfold localEmbed localInflate
    rw [if_pos hT, if_pos hin, if_pos hS]
  · by_cases hT : ∀ i, i ∉ T → x i = y i
    · have hin : ¬ ∀ i : T, i.1 ∉ S → x i.1 = y i.1 := by
        intro h
        apply hS
        intro i hiS
        by_cases hiT : i ∈ T
        · exact h ⟨i, hiT⟩ hiS
        · exact hT i hiT
      unfold localEmbed localInflate
      rw [if_pos hT, if_neg hin, if_neg hS]
    · unfold localEmbed
      rw [if_neg hT, if_neg hS]

theorem SupportedOn.mono {O : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hST : S ⊆ T) :
    SupportedOn O T := by
  obtain ⟨A, hA⟩ := hO
  exact ⟨localInflate S T hST A, hA.trans (localEmbed_localInflate S T hST A).symm⟩

/-- Split the unchanged physical tensor basis into supported and complementary sites. -/
def basisSplit (S : Finset (Fin n)) :
    PhysicalBasis n dim ≃ LocalBasis dim S × LocalBasis dim Sᶜ := by
  classical
  exact
    { toFun := fun x => (fun i => x i.1, fun i => x i.1)
      invFun := fun p i => if hi : i ∈ S then p.1 ⟨i, hi⟩
        else p.2 ⟨i, Finset.mem_compl.mpr hi⟩
      left_inv := by
        intro x
        funext i
        by_cases hi : i ∈ S <;> simp [hi]
      right_inv := by
        intro p
        apply Prod.ext
        · funext i
          simp [i.2]
        · funext i
          have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
          simp [hi] }

/-- The explicit embedding is exactly `A ⊗ I` under the physical-basis split. -/
theorem reindex_localEmbed (S : Finset (Fin n)) (A : Operator (LocalBasis dim S)) :
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A) =
      A ⊗ₖ (1 : Operator (LocalBasis dim Sᶜ)) := by
  classical
  ext p r
  change localEmbed S A ((basisSplit S).symm p) ((basisSplit S).symm r) =
    A p.1 r.1 * (1 : Operator (LocalBasis dim Sᶜ)) p.2 r.2
  have hp : (fun i : S => ((basisSplit S).symm p) i.1) = p.1 := by
    funext i
    simp [basisSplit, i.2]
  have hr : (fun i : S => ((basisSplit S).symm r) i.1) = r.1 := by
    funext i
    simp [basisSplit, i.2]
  have hout : (∀ i, i ∉ S → (basisSplit S).symm p i = (basisSplit S).symm r i) ↔
      p.2 = r.2 := by
    constructor
    · intro h
      funext i
      have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
      simpa [basisSplit, hi] using h i.1 hi
    · intro h i hi
      have he := congrFun h ⟨i, Finset.mem_compl.mpr hi⟩
      simpa [basisSplit, hi] using he
  by_cases hpr : p.2 = r.2 <;>
    simp [localEmbed, hout, hp, hr, Matrix.one_apply, hpr]

theorem localEmbed_mul (S : Finset (Fin n)) (A B : Operator (LocalBasis dim S)) :
    localEmbed S (A * B) = localEmbed S A * localEmbed S B := by
  classical
  apply (Matrix.reindexRingEquiv ℂ (basisSplit S)).injective
  rw [(Matrix.reindexRingEquiv ℂ (basisSplit S)).map_mul]
  change Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S (A * B)) =
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A) *
      Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S B)
  rw [reindex_localEmbed, reindex_localEmbed, reindex_localEmbed]
  simpa only [one_mul] using
    (Matrix.mul_kronecker_mul A B (1 : Operator (LocalBasis dim Sᶜ))
      (1 : Operator (LocalBasis dim Sᶜ)))

theorem reindex_localEmbed_compl (S : Finset (Fin n))
    (B : Operator (LocalBasis dim Sᶜ)) :
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed Sᶜ B) =
      (1 : Operator (LocalBasis dim S)) ⊗ₖ B := by
  classical
  ext p r
  change localEmbed Sᶜ B ((basisSplit S).symm p) ((basisSplit S).symm r) =
    (1 : Operator (LocalBasis dim S)) p.1 r.1 * B p.2 r.2
  have hp : (fun i : ↥(Sᶜ) => ((basisSplit S).symm p) i.1) = p.2 := by
    funext i
    have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
    simp [basisSplit, hi]
  have hr : (fun i : ↥(Sᶜ) => ((basisSplit S).symm r) i.1) = r.2 := by
    funext i
    have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
    simp [basisSplit, hi]
  have hout : (∀ i, i ∉ Sᶜ → (basisSplit S).symm p i = (basisSplit S).symm r i) ↔
      p.1 = r.1 := by
    constructor
    · intro h
      funext i
      have hi : i.1 ∉ Sᶜ := by simpa using i.2
      simpa [basisSplit, i.2] using h i.1 hi
    · intro h i hi
      have hiS : i ∈ S := by simpa using hi
      have he := congrFun h ⟨i, hiS⟩
      simpa [basisSplit, hiS] using he
  unfold localEmbed
  by_cases hpr : p.1 = r.1
  · have hcond := hout.mpr hpr
    rw [if_pos hcond, hp, hr]
    simp [Matrix.one_apply, hpr]
  · have hcond : ¬ ∀ i, i ∉ Sᶜ →
        (basisSplit S).symm p i = (basisSplit S).symm r i := by
      intro h
      exact hpr (hout.mp h)
    rw [if_neg hcond]
    simp [Matrix.one_apply, hpr]

theorem localEmbed_commute_compl (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) (B : Operator (LocalBasis dim Sᶜ)) :
    Commute (localEmbed S A) (localEmbed Sᶜ B) := by
  classical
  change localEmbed S A * localEmbed Sᶜ B = localEmbed Sᶜ B * localEmbed S A
  apply (Matrix.reindexRingEquiv ℂ (basisSplit S)).injective
  rw [(Matrix.reindexRingEquiv ℂ (basisSplit S)).map_mul,
    (Matrix.reindexRingEquiv ℂ (basisSplit S)).map_mul]
  change Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A) *
      Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed Sᶜ B) =
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed Sᶜ B) *
      Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A)
  simp only [reindex_localEmbed, reindex_localEmbed_compl]
  calc
    (A ⊗ₖ (1 : Operator (LocalBasis dim Sᶜ))) *
        ((1 : Operator (LocalBasis dim S)) ⊗ₖ B) =
        (A * 1) ⊗ₖ ((1 : Operator (LocalBasis dim Sᶜ)) * B) :=
      (Matrix.mul_kronecker_mul A 1 1 B).symm
    _ = ((1 : Operator (LocalBasis dim S)) * A) ⊗ₖ (B * 1) := by simp
    _ = ((1 : Operator (LocalBasis dim S)) ⊗ₖ B) *
        (A ⊗ₖ (1 : Operator (LocalBasis dim Sᶜ))) :=
      Matrix.mul_kronecker_mul 1 A B 1

theorem SupportedOn.mul_same {O P : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P S) :
    SupportedOn (O * P) S := by
  obtain ⟨A, rfl⟩ := hO
  obtain ⟨B, rfl⟩ := hP
  exact ⟨A * B, (localEmbed_mul S A B).symm⟩

/-- Products are supported on the union of their concrete tensor supports. -/
theorem SupportedOn.mul {O P : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P T) :
    SupportedOn (O * P) (S ∪ T) := by
  exact (hO.mono Finset.subset_union_left).mul_same
    (hP.mono Finset.subset_union_right)

theorem SupportedOn.conjugate {O U : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hU : SupportedOn U T) :
    SupportedOn (U * O * U.conjTranspose) (S ∪ T) := by
  have hO' : SupportedOn O (S ∪ T) := hO.mono Finset.subset_union_left
  have hU' : SupportedOn U (S ∪ T) := hU.mono Finset.subset_union_right
  exact (hU'.mul_same hO').mul_same hU'.conjTranspose

/-- Tensor-local operators on disjoint site sets commute. -/
theorem SupportedOn.commute {O P : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P T)
    (hST : Disjoint S T) : Commute O P := by
  classical
  have hTS : T ⊆ Sᶜ := by
    intro i hiT
    apply Finset.mem_compl.mpr
    intro hiS
    exact Finset.disjoint_left.mp hST hiS hiT
  obtain ⟨A, hA⟩ := hO
  obtain ⟨B, hB⟩ := hP.mono hTS
  rw [hA, hB]
  exact localEmbed_commute_compl S A B

theorem SupportedOn.conjugate_disjoint {O U : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hU : SupportedOn U T)
    (hST : Disjoint S T) (hunit : IsUnitary U) :
    U * O * U.conjTranspose = O := by
  have hc : O * U = U * O := hO.commute hU hST
  have hUU : U * U.conjTranspose = 1 := hunit.2
  rw [← hc, mul_assoc, hUU, mul_one]

theorem supportedOn_list_prod (gates : List (Operator (PhysicalBasis n dim)))
    (S : Finset (Fin n)) (h : ∀ A ∈ gates, SupportedOn A S) :
    SupportedOn gates.prod S := by
  revert h
  induction gates with
  | nil =>
      intro h
      simpa using supportedOn_one (dim := dim) S
  | cons A gates ih =>
      intro h
      have hA : SupportedOn A S := h A (by simp)
      have hg : ∀ B ∈ gates, SupportedOn B S := by
        intro B hB
        exact h B (by simp [hB])
      simpa using hA.mul_same (ih hg)

def Layer.supportUnion {q : ℕ} (L : Layer n dim q) : Finset (Fin n) :=
  Finset.univ.biUnion L.support

theorem Layer.eval_supportedOn {q : ℕ} (L : Layer n dim q) :
    SupportedOn L.eval L.supportUnion := by
  classical
  apply supportedOn_list_prod
  intro A hA
  have hA' : ∃ i, L.gate i = A := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hA
  obtain ⟨i, rfl⟩ := hA'
  apply (L.locality i).mono
  intro j hj
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩

def Layer.activeIndices {q : ℕ} (L : Layer n dim q) (S : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ¬ Disjoint (L.support i) S

/-- Sites already in the support, together with precisely the intersecting gates. -/
def Layer.lightCone {q : ℕ} (L : Layer n dim q) (S : Finset (Fin n)) :
    Finset (Fin n) := S ∪ (L.activeIndices S).biUnion L.support

theorem Layer.support_subset_lightCone_or_disjoint {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) (i : Fin n) :
    L.support i ⊆ L.lightCone S ∨ Disjoint (L.support i) (L.lightCone S) := by
  classical
  by_cases hi : Disjoint (L.support i) S
  · right
    apply Finset.disjoint_left.mpr
    intro x hxi hx
    rcases Finset.mem_union.mp hx with hxS | hxA
    · exact Finset.disjoint_left.mp hi hxi hxS
    · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hxA
      have hjact : ¬ Disjoint (L.support j) S := (Finset.mem_filter.mp hj).2
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hjact hi
      exact Finset.disjoint_left.mp (L.disjoint i j hij) hxi hxj
  · left
    intro x hx
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    exact ⟨i, by simp [Layer.activeIndices, hi], hx⟩

private theorem supportedOn_conjugate_prod
    (gates : List (Operator (PhysicalBasis n dim))) (S : Finset (Fin n))
    (hstep : ∀ U ∈ gates, ∀ P : Operator (PhysicalBasis n dim), SupportedOn P S →
      SupportedOn (U * P * U.conjTranspose) S)
    (O : Operator (PhysicalBasis n dim)) (hO : SupportedOn O S) :
    SupportedOn (gates.prod * O * gates.prod.conjTranspose) S := by
  revert hstep
  induction gates with
  | nil =>
      intro hstep
      simpa using hO
  | cons U gates ih =>
      intro hstep
      have hg : ∀ V ∈ gates, ∀ P : Operator (PhysicalBasis n dim), SupportedOn P S →
          SupportedOn (V * P * V.conjTranspose) S := by
        intro V hV P hP
        exact hstep V (by simp [hV]) P hP
      have hinner := ih hg
      have houter := hstep U (by simp) _ hinner
      simpa only [List.prod_cons, Matrix.conjTranspose_mul, mul_assoc] using houter

/-- The exact matrix light-cone law, proved by tensor commutation and cancellation. -/
theorem Layer.conjugate_supportedOn {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) {O : Operator (PhysicalBasis n dim)} (hO : SupportedOn O S) :
    SupportedOn (L.eval * O * L.eval.conjTranspose) (L.lightCone S) := by
  classical
  change SupportedOn (((List.ofFn L.gate).reverse).prod * O *
    (((List.ofFn L.gate).reverse).prod).conjTranspose) (L.lightCone S)
  apply supportedOn_conjugate_prod ((List.ofFn L.gate).reverse) (L.lightCone S)
    ?_ O (hO.mono Finset.subset_union_left)
  intro U hU P hP
  have hU' : ∃ i, L.gate i = U := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hU
  obtain ⟨i, rfl⟩ := hU'
  rcases L.support_subset_lightCone_or_disjoint S i with hsub | hdis
  · have hi : SupportedOn (L.gate i) (L.lightCone S) := (L.locality i).mono hsub
    exact (hi.mul_same hP).mul_same hi.conjTranspose
  · rw [hP.conjugate_disjoint (L.locality i) hdis.symm (L.unitary i)]
    exact hP

/-- The unique gate block containing a site, or that idle site's singleton. -/
def Layer.blockAt {q : ℕ} (L : Layer n dim q) (x : Fin n) : Finset (Fin n) := by
  classical
  exact if h : ∃ i, x ∈ L.support i then L.support (Classical.choose h) else {x}

theorem Layer.mem_blockAt {q : ℕ} (L : Layer n dim q) (x : Fin n) :
    x ∈ L.blockAt x := by
  classical
  unfold Layer.blockAt
  split_ifs with h
  · exact Classical.choose_spec h
  · simp

theorem Layer.blockAt_card_le {q : ℕ} (L : Layer n dim q) (x : Fin n) (hq : 1 ≤ q) :
    (L.blockAt x).card ≤ q := by
  classical
  unfold Layer.blockAt
  split_ifs with h
  · exact L.arity (Classical.choose h)
  · simpa using hq

theorem Layer.blockAt_eq_of_mem {q : ℕ} (L : Layer n dim q) (i : Fin n)
    (x : Fin n) (hx : x ∈ L.support i) : L.blockAt x = L.support i := by
  classical
  unfold Layer.blockAt
  split_ifs with h
  · have hci : Classical.choose h = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (L.disjoint _ _ hne) (Classical.choose_spec h) hx
    rw [hci]
  · exact False.elim (h ⟨i, hx⟩)

theorem Layer.lightCone_subset_blocks {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) : L.lightCone S ⊆ S.biUnion L.blockAt := by
  classical
  intro y hy
  rcases Finset.mem_union.mp hy with hyS | hyA
  · exact Finset.mem_biUnion.mpr ⟨y, hyS, L.mem_blockAt y⟩
  · obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hyA
    have hact : ¬ Disjoint (L.support i) S := (Finset.mem_filter.mp hi).2
    have hex : ∃ x, x ∈ L.support i ∧ x ∈ S := by
      by_contra hn
      apply hact
      apply Finset.disjoint_left.mpr
      intro x hxi hxS
      exact hn ⟨x, hxi, hxS⟩
    obtain ⟨x, hxi, hxS⟩ := hex
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hxS, ?_⟩
    rw [L.blockAt_eq_of_mem i x hxi]
    exact hyi

/-- Disjoint q-ary gates increase the number of supported sites by at most q. -/
theorem Layer.lightCone_card_le {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) (hq : 1 ≤ q) : (L.lightCone S).card ≤ q * S.card := by
  classical
  calc
    (L.lightCone S).card ≤ (S.biUnion L.blockAt).card :=
      Finset.card_le_card (L.lightCone_subset_blocks S)
    _ ≤ ∑ x ∈ S, (L.blockAt x).card := by apply Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, q := Finset.sum_le_sum fun x _ => L.blockAt_card_le x hq
    _ = q * S.card := by simp [Nat.mul_comm]

/-- Evaluation in physical execution order: the first listed layer acts first. -/
def layerSequenceEval {q : ℕ} : List (Layer n dim q) → Operator (PhysicalBasis n dim)
  | [] => 1
  | L :: layers => layerSequenceEval layers * L.eval

def layerSequenceCone {q : ℕ} : List (Layer n dim q) → Finset (Fin n) → Finset (Fin n)
  | [], S => S
  | L :: layers, S => layerSequenceCone layers (L.lightCone S)

theorem layerSequenceEval_eq_reverse_prod {q : ℕ} (layers : List (Layer n dim q)) :
    layerSequenceEval layers = (layers.map Layer.eval).reverse.prod := by
  induction layers with
  | nil => simp [layerSequenceEval]
  | cons L layers ih =>
      simp [layerSequenceEval, ih, List.reverse_cons, List.prod_append]

theorem layerSequence_conjugate_supportedOn {q : ℕ} (layers : List (Layer n dim q))
    (S : Finset (Fin n)) {O : Operator (PhysicalBasis n dim)} (hO : SupportedOn O S) :
    SupportedOn (layerSequenceEval layers * O * (layerSequenceEval layers).conjTranspose)
      (layerSequenceCone layers S) := by
  induction layers generalizing S O with
  | nil => simpa [layerSequenceEval, layerSequenceCone] using hO
  | cons L layers ih =>
      have hinner := L.conjugate_supportedOn S hO
      have houter := ih (L.lightCone S) hinner
      simpa only [layerSequenceEval, layerSequenceCone, Matrix.conjTranspose_mul,
        mul_assoc] using houter

theorem layerSequenceCone_card_le {q : ℕ} (layers : List (Layer n dim q))
    (S : Finset (Fin n)) (hq : 1 ≤ q) :
    (layerSequenceCone layers S).card ≤ q ^ layers.length * S.card := by
  induction layers generalizing S with
  | nil => simp [layerSequenceCone]
  | cons L layers ih =>
      calc
        (layerSequenceCone (L :: layers) S).card =
            (layerSequenceCone layers (L.lightCone S)).card := rfl
        _ ≤ q ^ layers.length * (L.lightCone S).card := ih (L.lightCone S)
        _ ≤ q ^ layers.length * (q * S.card) :=
          Nat.mul_le_mul_left _ (L.lightCone_card_le S hq)
        _ = q ^ (L :: layers).length * S.card := by
          simp only [List.length_cons, pow_succ]
          ring

end CriticalDepth.Manuscript
