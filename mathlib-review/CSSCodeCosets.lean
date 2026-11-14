import CSSCodeOrthogonality
import ShorRowAction

/-!
# Coset-state encoding of a binary CSS code

The logical basis is indexed by the quotient of the Z-check orthogonal
space by the X-check space. Every column is the normalized uniform
superposition over one coset.
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ} (H J : Submodule CSSBit (CSSWord n))

/-- The X checks as a subspace of the Z-check orthogonal space. -/
def insideChecks : Submodule CSSBit (cssOrthogonal J) :=
  H.comap (cssOrthogonal J).subtype

abbrev CSSCoset := (cssOrthogonal J) ⧸ insideChecks H J

instance : Fintype (CSSCoset H J) := by
  letI : Finite (CSSCoset H J) := Finite.of_surjective (insideChecks H J).mkQ
    (Submodule.mkQ_surjective (insideChecks H J))
  exact Fintype.ofFinite _

instance : DecidableEq (CSSCoset H J) := Classical.decEq _

def cosetRepresentative (b : CSSCoset H J) : cssOrthogonal J :=
  Classical.choose (Submodule.mkQ_surjective (insideChecks H J) b)

theorem cosetRepresentative_mk (b : CSSCoset H J) :
    (insideChecks H J).mkQ (cosetRepresentative H J b) = b :=
  Classical.choose_spec (Submodule.mkQ_surjective (insideChecks H J) b)

/-- The computational-basis support of a coset column. -/
def cosetWords (b : CSSCoset H J) : Finset (CSSWord n) := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ h : x ∈ cssOrthogonal J, (insideChecks H J).mkQ ⟨x, h⟩ = b

theorem mem_cosetWords (b : CSSCoset H J) (x : CSSWord n) :
    x ∈ cosetWords H J b ↔
      ∃ h : x ∈ cssOrthogonal J, (insideChecks H J).mkQ ⟨x, h⟩ = b := by
  classical
  unfold cosetWords
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem cosetWords_mem_mk (x : cssOrthogonal J) :
    x.val ∈ cosetWords H J ((insideChecks H J).mkQ x) :=
  (mem_cosetWords H J _ x.val).mpr ⟨x.property, rfl⟩

theorem cosetWords_unique (b c : CSSCoset H J) (x : CSSWord n)
    (hb : x ∈ cosetWords H J b) (hc : x ∈ cosetWords H J c) : b = c := by
  obtain ⟨hx, hxb⟩ := (mem_cosetWords H J b x).mp hb
  obtain ⟨_, hxc⟩ := (mem_cosetWords H J c x).mp hc
  exact hxb.symm.trans hxc

local instance : Fintype H := Fintype.ofFinite H

theorem cosetWords_card (hHJ : H ≤ cssOrthogonal J) (b : CSSCoset H J) :
    (cosetWords H J b).card = Fintype.card H := by
  classical
  let r := cosetRepresentative H J b
  let e : H ↪ CSSWord n :=
    ⟨fun a => r.val + a.val, fun _ _ hh => Subtype.ext (add_left_cancel hh)⟩
  have hset : cosetWords H J b = Finset.univ.map e := by
    ext x
    rw [mem_cosetWords]
    constructor
    · rintro ⟨hx, hxb⟩
      let u : cssOrthogonal J := ⟨x, hx⟩
      have hd : (insideChecks H J).mkQ (u - r) = 0 := by
        rw [map_sub, hxb, cosetRepresentative_mk, sub_self]
      have hInside : u - r ∈ insideChecks H J :=
        (Submodule.Quotient.mk_eq_zero (insideChecks H J)).mp hd
      have hH : (u - r).val ∈ H := hInside
      let a : H := ⟨x - r.val, hH⟩
      refine Finset.mem_map.mpr ⟨a, Finset.mem_univ _, ?_⟩
      change r.val + (x - r.val) = x
      abel
    · intro hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
      let y : cssOrthogonal J := ⟨a.val, hHJ a.property⟩
      refine ⟨(r + y).property, ?_⟩
      change (insideChecks H J).mkQ (r + y) = b
      have hy : (insideChecks H J).mkQ y = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr a.property
      rw [map_add, cosetRepresentative_mk, hy, add_zero]
  rw [hset, Finset.card_map, Finset.card_univ]

def cosetAmplitude : ℂ := (Real.sqrt ((Fintype.card H : ℝ)⁻¹) : ℂ)

theorem cosetAmplitude_square :
    star (cosetAmplitude H) * cosetAmplitude H = (Fintype.card H : ℂ)⁻¹ := by
  have hs : (Real.sqrt ((Fintype.card H : ℝ)⁻¹)) ^ 2 =
      (Fintype.card H : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hc : star (cosetAmplitude H) = cosetAmplitude H := Complex.conj_ofReal _
  rw [hc]
  simpa [pow_two, cosetAmplitude] using congrArg Complex.ofReal hs

private theorem card_checks_ne_zero : (Fintype.card H : ℂ) ≠ 0 := by
  have h : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨(0 : H)⟩
  exact_mod_cast h.ne'

theorem cosetAmplitude_ne_zero : cosetAmplitude H ≠ 0 := by
  intro hz
  have hh := cosetAmplitude_square H
  rw [hz, mul_zero] at hh
  exact (inv_ne_zero (card_checks_ne_zero H)) hh.symm

def cssCosetEncoding : Matrix (CSSWord n) (CSSCoset H J) ℂ :=
  fun x b => if x ∈ cosetWords H J b then cosetAmplitude H else 0

theorem cssCosetEncoding_isometry (hHJ : H ≤ cssOrthogonal J) :
    (cssCosetEncoding H J).conjTranspose * cssCosetEncoding H J = 1 := by
  classical
  ext a b
  change (∑ x : CSSWord n, star (cssCosetEncoding H J x a) * cssCosetEncoding H J x b) =
    (1 : Operator (CSSCoset H J)) a b
  by_cases hab : a = b
  · subst b
    have hpoint (x : CSSWord n) :
        star (cssCosetEncoding H J x a) * cssCosetEncoding H J x a =
          if x ∈ cosetWords H J a then (Fintype.card H : ℂ)⁻¹ else 0 := by
      by_cases hx : x ∈ cosetWords H J a
      · simpa only [cssCosetEncoding, ite_eq_left hx] using cosetAmplitude_square H
      · simp [cssCosetEncoding, hx]
    simp_rw [hpoint]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun x : CSSWord n => x ∈ cosetWords H J a) =
        cosetWords H J a := by ext; simp
    rw [hf, Finset.sum_const, nsmul_eq_mul, cosetWords_card H J hHJ,
      mul_inv_cancel₀ (card_checks_ne_zero H), Matrix.one_apply_eq]
  · have hpoint (x : CSSWord n) :
        star (cssCosetEncoding H J x a) * cssCosetEncoding H J x b = 0 := by
      by_cases ha : x ∈ cosetWords H J a
      · have hb : x ∉ cosetWords H J b := fun hb => hab (cosetWords_unique H J a b x ha hb)
        simp [cssCosetEncoding, hb]
      · simp [cssCosetEncoding, ha]
    simp_rw [hpoint]
    rw [Finset.sum_const_zero, Matrix.one_apply_ne hab]

#print axioms cosetWords_card
#print axioms cssCosetEncoding_isometry

end

end CriticalDepth.Manuscript20261114.CSSCode
