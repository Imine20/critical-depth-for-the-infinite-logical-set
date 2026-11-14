import CSSCodeCosets

/-!
# Entire CSS coset-state space

A word in the encoded subspace vanishes off the Z-check orthogonal
space and is constant under all X-check translations. These conditions
also suffice, as shown by explicitly reconstructing the logical
coefficients from coset representatives.
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ} (H J : Submodule CSSBit (CSSWord n))

theorem cssCosetEncoding_mulVec_on (w : CSSCoset H J → ℂ) (x : cssOrthogonal J) :
    (cssCosetEncoding H J).mulVec w x.val =
      cosetAmplitude H * w ((insideChecks H J).mkQ x) := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single ((insideChecks H J).mkQ x)]
  · have hx : x.val ∈ cosetWords H J ((insideChecks H J).mkQ x) :=
      cosetWords_mem_mk H J x
    change (if x.val ∈ cosetWords H J ((insideChecks H J).mkQ x)
      then cosetAmplitude H else 0) * w ((insideChecks H J).mkQ x) = _
    rw [ite_eq_left hx]
  · intro b _ hb
    have h : x.val ∉ cosetWords H J b := fun h =>
      hb (cosetWords_unique H J _ _ x.val h (cosetWords_mem_mk H J x))
    simp [cssCosetEncoding, h]
  · simp

theorem cssCosetEncoding_mulVec_off (w : CSSCoset H J → ℂ) (x : CSSWord n)
    (hx : x ∉ cssOrthogonal J) :
    (cssCosetEncoding H J).mulVec w x = 0 := by
  classical
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  intro b _
  have h : x ∉ cosetWords H J b := fun h => hx ((mem_cosetWords H J b x).mp h).choose
  simp [cssCosetEncoding, h]

/-- Every vector fixed by the binary checks lies in the coset-encoding range. -/
theorem cssCosetEncoding_range (hHJ : H ≤ cssOrthogonal J) :
    Set.range (fun w => (cssCosetEncoding H J).mulVec w) =
      {v | (∀ a ∈ H, ∀ x, v (x + a) = v x) ∧
        ∀ x, x ∉ cssOrthogonal J → v x = 0} := by
  classical
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change (∀ a ∈ H, ∀ x,
      (cssCosetEncoding H J).mulVec w (x + a) = (cssCosetEncoding H J).mulVec w x) ∧ _
    constructor
    · intro a ha x
      let z : cssOrthogonal J := ⟨a, hHJ ha⟩
      have hq : (insideChecks H J).mkQ z = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ha
      by_cases hx : x ∈ cssOrthogonal J
      · let y : cssOrthogonal J := ⟨x, hx⟩
        change (cssCosetEncoding H J).mulVec w (y + z).val =
          (cssCosetEncoding H J).mulVec w y.val
        rw [cssCosetEncoding_mulVec_on, cssCosetEncoding_mulVec_on, map_add, hq, add_zero]
      · have hxa : x + a ∉ cssOrthogonal J := by
          intro hy
          have hz := (cssOrthogonal J).sub_mem hy (hHJ ha)
          apply hx
          simpa only [add_sub_cancel_right] using hz
        rw [cssCosetEncoding_mulVec_off H J w _ hxa, cssCosetEncoding_mulVec_off H J w _ hx]
    · exact cssCosetEncoding_mulVec_off H J w
  · rintro ⟨hX, hZ⟩
    let w (b : CSSCoset H J) := (cosetAmplitude H)⁻¹ * v (cosetRepresentative H J b).val
    refine ⟨w, ?_⟩
    funext x
    change (cssCosetEncoding H J).mulVec w x = v x
    by_cases hx : x ∈ cssOrthogonal J
    · let u : cssOrthogonal J := ⟨x, hx⟩
      let b := (insideChecks H J).mkQ u
      let r := cosetRepresentative H J b
      change (cssCosetEncoding H J).mulVec w u.val = v x
      rw [cssCosetEncoding_mulVec_on]
      change cosetAmplitude H * ((cosetAmplitude H)⁻¹ * v r.val) = v x
      rw [← mul_assoc, mul_inv_cancel₀ (cosetAmplitude_ne_zero H), one_mul]
      have hq : (insideChecks H J).mkQ (u - r) = 0 := by
        rw [map_sub, cosetRepresentative_mk]
        change b - b = 0
        exact sub_self b
      have hp : u - r ∈ insideChecks H J :=
        (Submodule.Quotient.mk_eq_zero (insideChecks H J)).mp hq
      have hd : (u - r).val ∈ H := hp
      have hv := hX (u - r).val hd r.val
      change v (r.val + (x - r.val)) = v r.val at hv
      rw [add_comm r.val, sub_add_cancel] at hv
      exact hv.symm
    · rw [cssCosetEncoding_mulVec_off H J w _ hx, hZ x hx]

#print axioms cssCosetEncoding_range

end

end CriticalDepth.Manuscript20261114.CSSCode
