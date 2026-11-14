import CSSCheckSpaces
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Select a basis of coordinate functionals from left to right. The inverse
coordinate map gives a reduced row-echelon basis of the original subspace.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open Matrix Module
open scoped BigOperators Matrix

private def isPivotList {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2))
    (piv : Fin k → Fin n) : Prop :=
  (∀ i j, i < j → piv i < piv j) ∧
  (∀ i, A i (piv i) = 1) ∧
  (∀ i j, j < piv i → A i j = 0) ∧
  (∀ i j, i ≠ j → A i (piv j) = 0)

private instance isPivotList_decidable {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2))
    (piv : Fin k → Fin n) : Decidable (isPivotList A piv) := by
  unfold isPivotList
  have h₁ : Decidable (∀ i j : Fin k, i < j → piv i < piv j) :=
    @Fintype.decidableForallFintype _ _ (fun i =>
      @Fintype.decidableForallFintype _ _ (fun j => inferInstance) inferInstance) inferInstance
  have h₂ : Decidable (∀ i : Fin k, A i (piv i) = 1) :=
    @Fintype.decidableForallFintype _ _ (fun i => inferInstance) inferInstance
  have h₃ : Decidable (∀ (i : Fin k) (j : Fin n), j < piv i → A i j = 0) :=
    @Fintype.decidableForallFintype _ _ (fun i =>
      @Fintype.decidableForallFintype _ _ (fun j => inferInstance) inferInstance) inferInstance
  have h₄ : Decidable (∀ i j : Fin k, i ≠ j → A i (piv j) = 0) :=
    @Fintype.decidableForallFintype _ _ (fun i =>
      @Fintype.decidableForallFintype _ _ (fun j => inferInstance) inferInstance) inferInstance
  exact @instDecidableAnd _ _ h₁ (@instDecidableAnd _ _ h₂ (@instDecidableAnd _ _ h₃ h₄))

/-- Each row's pivot is one, its earlier entries vanish, and the other
rows vanish in that pivot column. Pivots increase with the row order. -/
def BinaryRREF {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2)) : Prop :=
  ∃ piv : Fin k → Fin n, isPivotList A piv

instance binaryRREF_decidable {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2)) :
    Decidable (BinaryRREF A) :=
  @Fintype.decidableExistsFintype _ (isPivotList A) (isPivotList_decidable A) inferInstance

private theorem exists_greedy_coordinates {M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] {n : ℕ} (f : Fin n → M) :
    ∃ S : Finset (Fin n), LinearIndepOn (ZMod 2) f (S : Set (Fin n)) ∧
      ∀ j : Fin n, f j ∈ Submodule.span (ZMod 2)
        (f '' {i | i ∈ S ∧ i ≤ j}) := by
  classical
  have step (m : ℕ) (hm : m ≤ n) :
      ∃ S : Finset (Fin n), (∀ i ∈ S, i.val < m) ∧
        LinearIndepOn (ZMod 2) f (S : Set (Fin n)) ∧
        ∀ j : Fin n, j.val < m → f j ∈ Submodule.span (ZMod 2)
          (f '' {i | i ∈ S ∧ i ≤ j}) := by
    induction m with
    | zero =>
      refine ⟨∅, by simp, ?_, by omega⟩
      simpa using (linearIndepOn_empty (ZMod 2) f)
    | succ m ih =>
      obtain ⟨S, hS, hInd, hSpan⟩ := ih (by omega)
      let j : Fin n := ⟨m, by omega⟩
      have hnot : j ∉ S := fun h => (Nat.lt_irrefl m) (hS j h)
      by_cases hj : f j ∈ Submodule.span (ZMod 2) (f '' (S : Set (Fin n)))
      · refine ⟨S, fun i hi => (hS i hi).trans (Nat.lt_succ_self m), hInd, ?_⟩
        intro i hi
        by_cases he : i.val < m
        · exact hSpan i he
        · have heq : i = j := Fin.ext (by change i.val = m; omega)
          subst i
          apply Submodule.span_mono (Set.image_mono ?_) hj
          intro k hk
          exact ⟨hk, (hS k hk).le⟩
      · refine ⟨insert j S, ?_, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Nat.lt_succ_self m
          · exact (hS i hi).trans (Nat.lt_succ_self m)
        · simpa only [Finset.coe_insert] using
            (linearIndepOn_insert hnot).mpr ⟨hInd, hj⟩
        · intro i hi
          by_cases he : i.val < m
          · apply Submodule.span_mono (Set.image_mono ?_) (hSpan i he)
            intro k hk
            exact ⟨Finset.mem_insert_of_mem hk.1, hk.2⟩
          · have heq : i = j := Fin.ext (by change i.val = m; omega)
            subst i
            exact Submodule.subset_span ⟨j, ⟨Finset.mem_insert_self _ _, le_rfl⟩, rfl⟩
  obtain ⟨S, _, hi, hS⟩ := step n le_rfl
  exact ⟨S, hi, fun j => hS j j.isLt⟩

/-- Every binary subspace has a full-row-rank reduced row-echelon basis. -/
theorem exists_binaryRREF_matrix {n k : ℕ} (H : Submodule (ZMod 2) ((Fin n → ZMod 2)))
    (hH : Module.finrank (ZMod 2) H = k) :
    ∃ A : Matrix (Fin k) (Fin n) (ZMod 2),
      BinaryRREF A ∧ Function.Injective A.vecMulLinear ∧ A.vecMulLinear.range = H := by
  classical
  let f (i : Fin n) : Module.Dual (ZMod 2) H := (LinearMap.proj i).comp H.subtype
  have hf (i : Fin n) (x : H) : f i x = x.val i := rfl
  have hSpan : Submodule.span (ZMod 2) (Set.range f) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro x hx
    have he : ∃ i, x.val i ≠ 0 := by
      by_contra! h
      exact hx (Subtype.ext (funext h))
    obtain ⟨i, hi⟩ := he
    exact ⟨f i, ⟨i, rfl⟩, hi⟩
  obtain ⟨S, hInd, hGreedy⟩ := exists_greedy_coordinates f
  have hTop : Submodule.span (ZMod 2) (Set.range fun i : S => f i.val) = ⊤ := by
    rw [← hSpan]
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.span_mono ?_ (hGreedy i)
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj.1⟩, rfl⟩
  let basisS : Basis (↥S) (ZMod 2) (Module.Dual (ZMod 2) H) :=
    Basis.mk hInd hTop.ge
  have hcard : S.card = k := by
    have h := Module.finrank_eq_card_basis basisS
    rw [Subspace.dual_finrank_eq, hH] at h
    simpa only [Fintype.card_coe] using h.symm
  let e := S.orderIsoOfFin hcard
  let b := basisS.reindex e.symm.toEquiv
  let piv (i : Fin k) := (e i).val
  have hPiv (i : Fin k) : b i = f (piv i) := by
    simp [b, basisS, piv]
  have hs : StrictMono piv := fun i j hij => e.strictMono hij
  let u : Fin k → H :=
    fun i => (Module.evalEquiv (ZMod 2) H).symm (b.dualBasis i)
  have hDelta (i j : Fin k) : f (piv j) (u i) = if j = i then 1 else 0 := by
    rw [← hPiv]
    exact (Module.apply_evalEquiv_symm_apply _ _ _ _).trans (b.dualBasis_apply_self i j)
  let A : Matrix (Fin k) (Fin n) (ZMod 2) := fun i j => (u i).val j
  have hZero (i : Fin k) (j : Fin n) (hj : j < piv i) : A i j = 0 := by
    change f j (u i) = 0
    let E := Module.Dual.eval (ZMod 2) H (u i)
    have hs₀ : Submodule.span (ZMod 2) (f '' {r | r ∈ S ∧ r ≤ j}) ≤ E.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨r, hr, rfl⟩
      let k₀ := e.symm ⟨r, hr.1⟩
      have hp : piv k₀ = r := congrArg Subtype.val (e.apply_symm_apply ⟨r, hr.1⟩)
      have hne : k₀ ≠ i := by
        intro hh
        rw [hh] at hp
        have hle : piv i ≤ j := hp.symm ▸ hr.2
        exact (not_lt_of_ge hle) hj
      change f r (u i) = 0
      rw [← hp, hDelta, if_neg hne]
    exact hs₀ (hGreedy j)
  have hrref : BinaryRREF A := by
    refine ⟨piv, hs, ?_, hZero, ?_⟩
    · intro i
      change f (piv i) (u i) = _
      simp [hDelta]
    · intro i j hij
      change f (piv j) (u i) = _
      rw [hDelta, if_neg hij.symm]
  let B := b.dualBasis.map (Module.evalEquiv (ZMod 2) H).symm
  have hcoeff (t : Fin k → ZMod 2) : A.vecMulLinear t = ((B.equivFun.symm t : H) : (Fin n → ZMod 2)) := by
    funext j
    have h := congrArg (fun x : H => x.val j) (B.equivFun_symm_apply t)
    change (∑ i, t i * (u i).val j) = ((B.equivFun.symm t : H) : (Fin n → ZMod 2)) j
    simpa only [B, u, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply, Module.Basis.map_apply] using h.symm
  refine ⟨A, hrref, fun x y h => B.equivFun.symm.injective (Subtype.ext ?_), ?_⟩
  · exact (hcoeff x).symm.trans (h.trans (hcoeff y))
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      rw [hcoeff]
      exact (B.equivFun.symm t).property
    · intro hx
      refine ⟨B.equivFun ⟨x, hx⟩, ?_⟩
      rw [hcoeff, LinearEquiv.symm_apply_apply]

#print axioms exists_binaryRREF_matrix

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
