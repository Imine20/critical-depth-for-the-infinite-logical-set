import CriticalDepthMathlib
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Binary symplectic elimination

At each step a nonzero vector and a vector pairing to one split off a
hyperbolic plane. The same operation recurses on its orthogonal complement.
-/

open LinearMap Module
open scoped BigOperators

namespace CriticalDepth.Manuscript20261114

abbrev PauliBit := ZMod 2

/-- Two arrays of symplectic generators in a common pairing. -/
structure BinarySymplecticFrame {V : Type*} [AddCommGroup V] [Module PauliBit V]
    (B : LinearMap.BilinForm PauliBit V) (k : ℕ) where
  X : Fin k → V
  Z : Fin k → V
  xPair : ∀ i j, B (X i) (X j) = 0
  zPair : ∀ i j, B (Z i) (Z j) = 0
  crossPair : ∀ i j, B (X i) (Z j) = if i = j then 1 else 0

private theorem pauliBit_eq_zero_or_one (s : PauliBit) : s = 0 ∨ s = 1 := by decide +revert

private theorem alternating_binary_symm {V : Type*} [AddCommGroup V] [Module PauliBit V]
    (B : LinearMap.BilinForm PauliBit V) (hB : B.IsAlt) (x y : V) : B x y = B y x := by
  have h := hB.neg_eq (x := x) (y := y)
  rcases pauliBit_eq_zero_or_one (B x y) with he | he
  · simpa only [he, neg_zero] using h
  · simpa only [he, show -(1 : PauliBit) = 1 by decide] using h

private def planeMap {V : Type*} [AddCommGroup V] [Module PauliBit V]
    (x z : V) : (PauliBit × PauliBit) →ₗ[PauliBit] V where
  toFun a := a.1 • x + a.2 • z
  map_add' a b := by
    change (a.1+b.1) • x + (a.2+b.2) • z = (a.1 • x+a.2 • z)+(b.1 • x+b.2 • z)
    simp only [add_smul]
    abel
  map_smul' c a := by
    change (c*a.1) • x + (c*a.2) • z = c • (a.1 • x+a.2 • z)
    rw [smul_add, mul_smul, mul_smul]

private theorem pair_left {V : Type*} [AddCommGroup V] [Module PauliBit V]
    (B : LinearMap.BilinForm PauliBit V) (hB : B.IsAlt) {x z : V} (hxz : B x z = 1)
    (a : PauliBit × PauliBit) : B x (planeMap x z a) = a.2 := by
  change B x (a.1 • x + a.2 • z) = a.2
  rw [map_add, map_smul, map_smul, hB.self_eq_zero, hxz]
  simp [smul_eq_mul]

private theorem pair_right {V : Type*} [AddCommGroup V] [Module PauliBit V]
    (B : LinearMap.BilinForm PauliBit V) (hB : B.IsAlt) {x z : V} (hxz : B x z = 1)
    (a : PauliBit × PauliBit) : B z (planeMap x z a) = a.1 := by
  have hzx : B z x = 1 := (alternating_binary_symm B hB z x).trans hxz
  change B z (a.1 • x + a.2 • z) = a.1
  rw [map_add, map_smul, map_smul, hB.self_eq_zero, hzx]
  simp [smul_eq_mul]

/-- Hyperbolic Gram–Schmidt elimination in characteristic two. The lower
bound on dimension allows partial frames as well as full frames. -/
theorem binarySymplecticFrame_nonempty (k : ℕ) {V : Type*}
    [AddCommGroup V] [Module PauliBit V] [FiniteDimensional PauliBit V]
    (B : LinearMap.BilinForm PauliBit V) (hAlt : B.IsAlt) (hNondeg : B.Nondegenerate)
    (hk : 2 * k ≤ finrank PauliBit V) : Nonempty (BinarySymplecticFrame B k) := by
  induction k generalizing V with
  | zero =>
    exact ⟨⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
    have hpos : 0 < finrank PauliBit V := by omega
    letI : Nontrivial V := finrank_pos_iff.mp hpos
    obtain ⟨x,hx⟩ := exists_ne (0 : V)
    have hex : ∃ z : V, B x z ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hx (hNondeg.1 x hn)
    obtain ⟨z,hz⟩ := hex
    have hxz : B x z = 1 := (pauliBit_eq_zero_or_one _).resolve_left hz
    let L := planeMap x z
    let W := LinearMap.range L
    let R := B.orthogonal W
    have hL : Function.Injective L := by
      intro a b h
      apply Prod.ext
      · exact (pair_right B hAlt hxz a).symm.trans
          ((congrArg (B z) h).trans (pair_right B hAlt hxz b))
      · exact (pair_left B hAlt hxz a).symm.trans
          ((congrArg (B x) h).trans (pair_left B hAlt hxz b))
    have hW : finrank PauliBit W = 2 := by
      change finrank PauliBit (LinearMap.range L) = 2
      rw [LinearMap.finrank_range_of_inj hL, Module.finrank_prod]
      simp
    have hxW : x ∈ W := ⟨(1,0), by simp [L, planeMap]⟩
    have hzW : z ∈ W := ⟨(0,1), by simp [L, planeMap]⟩
    have hD : Disjoint W R := by
      apply Submodule.disjoint_def.mpr
      rintro v ⟨a,rfl⟩ hv
      have ha : a.1 = 0 := (pair_right B hAlt hxz a).symm.trans (hv z hzW)
      have hb : a.2 = 0 := (pair_left B hAlt hxz a).symm.trans (hv x hxW)
      have he : a = 0 := Prod.ext ha hb
      rw [he, map_zero]
    have hRdim : 2 * k ≤ finrank PauliBit R := by
      have he := Submodule.finrank_add_eq_of_isCompl
        ((LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hAlt.isRefl).mpr hD)
      change finrank PauliBit W + finrank PauliBit R = finrank PauliBit V at he
      omega
    have hRnondeg : (B.restrict R).Nondegenerate := by
      apply LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hAlt.isRefl
      change Disjoint R (B.orthogonal (B.orthogonal W))
      rw [LinearMap.BilinForm.orthogonal_orthogonal hNondeg hAlt.isRefl]
      exact hD.symm
    have hRalt : (B.restrict R).IsAlt := fun y => hAlt.self_eq_zero y.val
    obtain ⟨F⟩ := ih (B.restrict R) hRalt hRnondeg hRdim
    let X : Fin (k+1) → V := Fin.cons x (fun i => (F.X i).val)
    let Z : Fin (k+1) → V := Fin.cons z (fun i => (F.Z i).val)
    refine ⟨⟨X,Z,?_,?_,?_⟩⟩
    · intro i j
      refine Fin.cases (Fin.cases ?_ (fun j => ?_) j)
        (fun i => Fin.cases ?_ (fun j => ?_) j) i
      · exact hAlt.self_eq_zero x
      · exact (F.X j).property x hxW
      · exact (alternating_binary_symm B hAlt _ _).trans ((F.X i).property x hxW)
      · exact F.xPair i j
    · intro i j
      refine Fin.cases (Fin.cases ?_ (fun j => ?_) j)
        (fun i => Fin.cases ?_ (fun j => ?_) j) i
      · exact hAlt.self_eq_zero z
      · exact (F.Z j).property z hzW
      · exact (alternating_binary_symm B hAlt _ _).trans ((F.Z i).property z hzW)
      · exact F.zPair i j
    · intro i j
      refine Fin.cases (Fin.cases ?_ (fun j => ?_) j)
        (fun i => Fin.cases ?_ (fun j => ?_) j) i
      · simpa [X,Z] using hxz
      · simpa [X,Z, Ne.symm (Fin.succ_ne_zero j)] using (F.Z j).property x hxW
      · have h := (alternating_binary_symm B hAlt (F.X i).val z).trans ((F.X i).property z hzW)
        simpa [X,Z, Fin.succ_ne_zero i] using h
      · simpa [X,Z] using F.crossPair i j

#print axioms binarySymplecticFrame_nonempty

end CriticalDepth.Manuscript20261114
