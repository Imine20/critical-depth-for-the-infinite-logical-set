import CSSMonomialLocality
import CSSCodeEncoding
import CSSCodeCosetRange

/-!
# The action of monomial matrices on CSS cosets
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCode
open Matrix

variable {n : ℕ}

theorem binaryMonomial_apply_mulVec
    {U : Operator (QubitBasis n)} {f : Equiv.Perm (BinaryWord (Fin n))}
    {u : BinaryWord (Fin n) → ℂˣ} (hm : binaryMonomial U f u)
    (v : QubitBasis n → ℂ) (y : BinaryWord (Fin n)) :
    (U.mulVec v) ((binaryWordEquiv n).symm (f y)) =
      (u y : ℂ) * v ((binaryWordEquiv n).symm y) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single ((binaryWordEquiv n).symm y)]
  · rw [hm, ite_eq_left rfl]
  · intro j _ hj
    let z := (binaryWordEquiv n) j
    have he : (binaryWordEquiv n).symm z = j := Equiv.symm_apply_apply _ _
    have hz : f y ≠ f z := fun hf => hj (he.symm.trans
      (congrArg (binaryWordEquiv n).symm (f.injective hf).symm))
    rw [← he, hm, ite_eq_right hz, zero_mul]
  · simp

/-- If a monomial matrix preserves the CSS range, both the support and
coefficients of each uniformly weighted coset are carried to a coset.
No spectral approximation is used. -/
theorem binaryMonomial_preserves_cosets_and_phases
    (H L : Submodule (ZMod 2) (BinaryWord (Fin n))) (hHL : H ≤ L)
    {U : Operator (QubitBasis n)} {f : Equiv.Perm (BinaryWord (Fin n))}
    {u : BinaryWord (Fin n) → ℂˣ} (hm : binaryMonomial U f u)
    (hRange : ∀ x ∈ L,
      ∃ y ∈ L, (∀ z, f z + y ∈ H ↔ z + x ∈ H) ∧
        ∀ z, z + x ∈ H → u z = u x) :
    (∀ a ∈ H, ∀ x ∈ L, f (x + a) + f x ∈ H) ∧
    ∀ a ∈ H, ∀ x ∈ L, u (x + a) = u x := by
  have cancels (a : BinaryWord (Fin n)) : a + a = 0 := by
    funext i
    exact (by decide : ∀ b : ZMod 2, b + b = 0) _
  constructor
  · intro a ha x hx
    obtain ⟨y, _, hmap, _⟩ := hRange x hx
    have hxa : x + a + x ∈ H := by
      rwa [add_right_comm, cancels, zero_add]
    have hf₁ := (hmap (x + a)).mpr hxa
    have hf₀ := (hmap x).mpr (by rw [cancels]; exact H.zero_mem)
    have he : (f (x + a) + y) + (f x + y) = f (x + a) + f x := by
      rw [add_add_add_comm, cancels, add_zero]
    exact he ▸ H.add_mem hf₁ hf₀
  · intro a ha x hx
    obtain ⟨_, _, _, hphase⟩ := hRange x hx
    apply hphase
    rwa [add_right_comm, cancels, zero_add]

#print axioms binaryMonomial_apply_mulVec
#print axioms binaryMonomial_preserves_cosets_and_phases

/-- It suffices to check the action on the unnormalized indicator of
each coset. Such an indicator is in the physical CSS range by the
range characterization. -/
theorem binaryMonomial_preserves_cssWordCosets
    (H L : Submodule (ZMod 2) (BinaryWord (Fin n))) (hHL : H ≤ L)
    {U : Operator (QubitBasis n)} {f : Equiv.Perm (BinaryWord (Fin n))}
    {u : BinaryWord (Fin n) → ℂˣ} (hm : binaryMonomial U f u)
    (hRange : ∀ v : QubitBasis n → ℂ,
      (∀ a ∈ H, ∀ x, v ((binaryWordEquiv n).symm (x + a)) = v ((binaryWordEquiv n).symm x)) →
      (∀ x, x ∉ L → v ((binaryWordEquiv n).symm x) = 0) →
      (∀ a ∈ H, ∀ x, (U.mulVec v) ((binaryWordEquiv n).symm (x + a)) =
        (U.mulVec v) ((binaryWordEquiv n).symm x)) ∧
      ∀ x, x ∉ L → (U.mulVec v) ((binaryWordEquiv n).symm x) = 0) :
    (∀ a ∈ H, ∀ x ∈ L, f (x + a) + f x ∈ H) ∧
    ∀ a ∈ H, ∀ x ∈ L, u (x + a) = u x := by
  classical
  have cancels (a : BinaryWord (Fin n)) : a + a = 0 := by
    funext i
    exact (by decide : ∀ b : ZMod 2, b + b = 0) _
  exact by
    have packed (a x : BinaryWord (Fin n)) (ha : a ∈ H) (hx : x ∈ L) :
        f (x + a) + f x ∈ H ∧ u (x + a) = u x := by
      let e := binaryWordEquiv n
      let support : Finset (BinaryWord (Fin n)) := Finset.univ.filter fun z => z + x ∈ H
      let v : QubitBasis n → ℂ := fun y => if e y + x ∈ H then 1 else 0
      have vAt (z : BinaryWord (Fin n)) : v (e.symm z) = if z + x ∈ H then 1 else 0 := by
        simp [v, e]
      have hVin : ∀ b ∈ H, ∀ z, v (e.symm (z + b)) = v (e.symm z) := by
        intro b hb z
        rw [vAt, vAt, add_right_comm z b x]
        split <;> split
        · rfl
        · rename_i hh hh'
          have hh'' := H.add_mem hh hb
          rw [add_assoc, cancels, add_zero] at hh''
          exact (hh' hh'').elim
        · rename_i hh hh'
          exact (hh (H.add_mem hh' hb)).elim
        · rfl
      have hVout : ∀ z, z ∉ L → v (e.symm z) = 0 := by
        intro z hz
        rw [vAt, if_neg]
        intro hs
        have h := L.add_mem (hHL hs) hx
        exact hz (by simpa [add_assoc, cancels, add_zero] using h)
      obtain ⟨hout, hzero⟩ := hRange v hVin hVout
      have hvx : v (e.symm x) = 1 := by rw [vAt, cancels, if_pos H.zero_mem]
      have hvxa : v (e.symm (x + a)) = 1 := (hVin a ha x).trans hvx
      have hUx : (U.mulVec v) (e.symm (f x)) = (u x : ℂ) := by
        rw [binaryMonomial_apply_mulVec hm, hvx, mul_one]
      have range_in (z : BinaryWord (Fin n)) (hz : z ∈ support) :
          f z ∈ Finset.univ.filter (fun y => (U.mulVec v) (e.symm y) ≠ 0) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [binaryMonomial_apply_mulVec hm, vAt, if_pos ((Finset.mem_filter.mp hz).2), mul_one]
        exact Units.ne_zero (u z)
      let outSupport := Finset.univ.filter (fun y => (U.mulVec v) (e.symm y) ≠ 0)
      have hSame : outSupport = support.map f.toEmbedding := by
        ext y
        obtain ⟨z, rfl⟩ := f.surjective y
        have he : f z ∈ support.map f.toEmbedding ↔ z ∈ support := by simp
        rw [he]
        by_cases hz : z ∈ support
        · exact ⟨fun _ => hz, fun _ => range_in z hz⟩
        · have hnot : z + x ∉ H := fun h => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hval : (U.mulVec v) (e.symm (f z)) = 0 := by
            rw [binaryMonomial_apply_mulVec hm, vAt, ite_eq_right hnot, mul_zero]
          simp [outSupport, hval, hz]
      have hsCard : support.card = Fintype.card H := by
        apply le_antisymm
        · let t : support → H := fun z => ⟨z.val + x, (Finset.mem_filter.mp z.property).2⟩
          have ht : Function.Injective t := fun z z' hh =>
            Subtype.ext (add_right_cancel (congrArg Subtype.val hh))
          simpa using Fintype.card_le_of_injective t ht
        · let t : H → support := fun z =>
            ⟨z.val + x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              simpa [add_assoc, cancels, add_zero] using z.property⟩⟩
          have ht : Function.Injective t := fun z z' hh =>
            Subtype.ext (add_right_cancel (congrArg Subtype.val hh))
          simpa using Fintype.card_le_of_injective t ht
      have hsubset : (Finset.univ : Finset H).image (fun b => f x + b.val) ⊆ outSupport := by
        intro z hz
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [hout b.val b.property, hUx]
          exact Units.ne_zero (u x)⟩
      have hcardOut : outSupport.card = Fintype.card H := by rw [hSame, Finset.card_map, hsCard]
      have hcardIn : ((Finset.univ : Finset H).image (fun b => f x + b.val)).card = Fintype.card H := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro b b' hb
          exact Subtype.ext (add_left_cancel hb)
      have hc := Finset.eq_of_subset_of_card_le hsubset (by rw [hcardOut, hcardIn])
      have hxa : x + a ∈ support := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rwa [add_right_comm, cancels, zero_add]
      have hfxa : f (x + a) ∈ outSupport := range_in _ hxa
      rw [← hc] at hfxa
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hfxa
      refine ⟨?_, ?_⟩
      · rw [← hb, add_right_comm, cancels, zero_add]
        exact b.property
      · apply Units.ext
        have he := hout b.val b.property (f x)
        rw [hb, binaryMonomial_apply_mulVec hm, hvxa, mul_one, hUx] at he
        exact he
    exact ⟨fun a ha x hx => (packed a x ha hx).1, fun a ha x hx => (packed a x ha hx).2⟩

#print axioms binaryMonomial_preserves_cssWordCosets

end CriticalDepth.Manuscript20261114.CSSCheckSpaces