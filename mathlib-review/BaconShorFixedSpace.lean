import BaconShorSubsystemEncoding
import ShorPhysicalZChecks
import PauliGroup

/-!
# Common fixed space of the Bacon--Shor center

The center's Z checks select computational words with uniform row parity.
The center's X translations identify exactly the words with the same
protected bit and gauge coordinates.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.PauliGroup
open scoped BigOperators

noncomputable section

variable {m b : ℕ}

private theorem baconOrbitAmplitude_ne_zero : orbitAmplitude b ≠ 0 := by
  intro hz
  have hn : (orbitCount b : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (CenterCoordinate b)).ne'
  have h := orbitAmplitude_square b
  rw [hz, mul_zero] at h
  exact (inv_ne_zero hn) h.symm

private theorem baconBinaryEncoding_mulVec_of_coordinates
    (w : Bit × Interior m b → ℂ) (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b) :
    (baconBinaryEncoding m b).mulVec w (baconWord ℓ u t) =
      orbitAmplitude b * w (ℓ,u) := by
  classical
  let x := baconWord ℓ u t
  have hx : x ∈ orbitWords ℓ u := (orbitWords_mem _ _ _).mpr ⟨t,rfl⟩
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single (ℓ,u)]
  · change (if x ∈ orbitWords ℓ u then orbitAmplitude b else 0) * w (ℓ,u) = _
    rw [ite_eq_left hx]
  · rintro ⟨k,v⟩ _ hne
    have hn : x ∉ orbitWords k v := by
      intro h
      obtain ⟨h₁,h₂⟩ := orbitWords_unique k ℓ v u x h hx
      exact hne (Prod.ext h₁ h₂)
    change (if x ∈ orbitWords k v then orbitAmplitude b else 0) * w (k,v) = _
    rw [ite_eq_right hn, zero_mul]
  · simp

private theorem baconBinaryEncoding_mulVec_off (w : Bit × Interior m b → ℂ)
    (x : BaconMask m b) (hx : ¬ ∀ i, rowParity x i = rowParity x 0) :
    (baconBinaryEncoding m b).mulVec w x = 0 := by
  classical
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  rintro ⟨ℓ,u⟩ _
  have hn : x ∉ orbitWords ℓ u := by
    rintro h
    obtain ⟨t, ht⟩ := (orbitWords_mem _ _ _).mp h
    apply hx
    intro i
    rw [← ht, baconWord_rowParity, baconWord_rowParity]
  change (if x ∈ orbitWords ℓ u then orbitAmplitude b else 0) * w (ℓ,u) = 0
  rw [ite_eq_right hn, zero_mul]

private theorem baconCenterX_gaugeBits (a : BaconMask m b) (ha : centerX a) :
    gaugeBits a = 0 := by
  funext i j
  change a (i.succ,j.succ) - a (0,j.succ) = 0
  rw [((centerX_iff a 0).mp ha).2 j.succ i.succ 0, sub_self]

private theorem baconWord_sub_centerX (ℓ : Bit) (u : Interior m b)
    (t s : CenterCoordinate b) :
    centerX (baconWord ℓ u t - baconWord ℓ u s) := by
  let x := baconWord ℓ u t
  let y := baconWord ℓ u s
  apply (centerX_iff (x-y) 0).mpr
  constructor
  · intro i
    change rowParity (x-y) i = 0
    rw [show rowParity (x-y) i = rowParity x i - rowParity y i by
      simp [rowParity, Pi.sub_apply, Finset.sum_sub_distrib]]
    simp [x, y, baconWord_rowParity]
  · intro j i k
    have h (i : Fin (m+1)) (j : Fin b) : (x-y) (i,j.succ) = t j - s j := by
      refine Fin.cases rfl (fun r => ?_) i
      change (t j + u r j) - (s j + u r j) = _
      abel
    refine Fin.cases ?_ (fun j => (h i j).trans (h k j).symm) j
    change (ℓ - ∑ j : Fin b, x (i,j.succ)) - (ℓ - ∑ j : Fin b, y (i,j.succ)) =
      (ℓ - ∑ j : Fin b, x (k,j.succ)) - (ℓ - ∑ j : Fin b, y (k,j.succ))
    calc
      _ = -(∑ j : Fin b, (x-y) (i,j.succ)) := by
        rw [show (∑ j : Fin b, (x-y) (i,j.succ)) =
          (∑ j : Fin b, x (i,j.succ)) - (∑ j : Fin b, y (i,j.succ)) by
            simp [Pi.sub_apply, Finset.sum_sub_distrib]]
        abel
      _ = -(∑ j : Fin b, (x-y) (k,j.succ)) := by simp_rw [h]
      _ = _ := by
        rw [show (∑ j : Fin b, (x-y) (k,j.succ)) =
          (∑ j : Fin b, x (k,j.succ)) - (∑ j : Fin b, y (k,j.succ)) by
            simp [Pi.sub_apply, Finset.sum_sub_distrib]]
        abel

private theorem baconBinaryEncoding_range :
    Set.range (fun w => (baconBinaryEncoding m b).mulVec w) =
      {v | (∀ a : BaconMask m b, centerX a → ∀ x, v (x+a) = v x) ∧
        ∀ x, (¬ ∀ i, rowParity x i = rowParity x 0) → v x = 0} := by
  classical
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨?_, baconBinaryEncoding_mulVec_off w⟩
    intro a ha x
    change (baconBinaryEncoding m b).mulVec w (x+a) = (baconBinaryEncoding m b).mulVec w x
    have hrow (y : BaconMask m b) (i : Fin (m+1)) :
        rowParity (y+a) i = rowParity y i := by
      have hv : rowParity a i = 0 := ((centerX_iff a 0).mp ha).1 i
      have he : rowParity (y+a) i = rowParity y i + rowParity a i := by
        simp [rowParity, Pi.add_apply, Finset.sum_add_distrib]
      rw [he, hv, add_zero]
    by_cases hx : ∀ i, rowParity x i = rowParity x 0
    · obtain ⟨⟨ℓ,u,t⟩, heq⟩ := baconWordEquiv.surjective ⟨x,hx⟩
      have hval : baconWord ℓ u t = x := congrArg Subtype.val heq
      rw [← hval, baconWord_add_gaugeX _ _ _ a ((centerX_iff a 0).mp ha).1,
        baconCenterX_gaugeBits a ha, add_zero, baconBinaryEncoding_mulVec_of_coordinates,
        baconBinaryEncoding_mulVec_of_coordinates]
    · have hy : ¬ ∀ i, rowParity (x+a) i = rowParity (x+a) 0 := by simpa only [hrow]
      rw [baconBinaryEncoding_mulVec_off w _ hy, baconBinaryEncoding_mulVec_off w _ hx]
  · rintro ⟨hX,hZ⟩
    refine ⟨fun a => (orbitAmplitude b)⁻¹ * v (baconWord a.1 a.2 0), ?_⟩
    funext x
    change (baconBinaryEncoding m b).mulVec
      (fun a => (orbitAmplitude b)⁻¹ * v (baconWord a.1 a.2 0)) x = v x
    by_cases hx : ∀ i, rowParity x i = rowParity x 0
    · obtain ⟨⟨ℓ,u,t⟩, heq⟩ := baconWordEquiv.surjective ⟨x,hx⟩
      have hval : baconWord ℓ u t = x := congrArg Subtype.val heq
      rw [← hval, baconBinaryEncoding_mulVec_of_coordinates, ← mul_assoc,
        mul_inv_cancel₀ baconOrbitAmplitude_ne_zero, one_mul]
      have h := hX _ (baconWord_sub_centerX ℓ u t 0) (baconWord ℓ u 0)
      rw [add_comm (baconWord ℓ u 0), sub_add_cancel] at h
      exact h.symm
    · rw [baconBinaryEncoding_mulVec_off _ _ hx, hZ x hx]

private theorem baconPhysicalEncoding_mulVec (w : Bit × Interior m b → ℂ)
    (x : QubitBasis ((m+1)*(b+1))) :
    (baconPhysicalEncoding m b).mulVec
        (w ∘ Equiv.prodCongr qubitBitEquiv (gaugeTupleEquiv m b)) x =
      (baconBinaryEncoding m b).mulVec w (shorBasisEquiv (m+1) (b+1) x) := by
  unfold Matrix.mulVec dotProduct
  exact (Equiv.prodCongr qubitBitEquiv (gaugeTupleEquiv m b)).sum_comp
    (fun a => baconBinaryEncoding m b (shorBasisEquiv (m+1) (b+1) x) a * w a)

private theorem rowPair_is_centerZ (i j : Fin (m+1)) :
    centerZ (rowPairZMask (columns := b+1) i j) := by
  refine ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0), ?_, rfl⟩
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', show (1 : Bit) + 1 = 0 from by decide]

/-- This is the entire fixed space of the physical Pauli center. -/
theorem baconPhysicalEncoding_range_eq_center :
    Set.range (fun w => (baconPhysicalEncoding m b).mulVec w) =
      {v | (∀ a : BaconMask m b, centerX a →
          (pauliMatrix 0 (physicalXWord a)).mulVec v = v) ∧
        ∀ z : BaconMask m b, centerZ z → (pauliMatrix 0 (physicalZWord z)).mulVec v = v} := by
  classical
  let e := shorBasisEquiv (m+1) (b+1)
  let k := Equiv.prodCongr qubitBitEquiv (gaugeTupleEquiv m b)
  ext v
  let u := v ∘ e.symm
  have hv : u ∘ e = v := by
    funext x
    exact congrArg v (e.symm_apply_apply x)
  have hr :
      v ∈ Set.range (fun w => (baconPhysicalEncoding m b).mulVec w) ↔
        u ∈ Set.range (fun w => (baconBinaryEncoding m b).mulVec w) := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w ∘ k.symm, ?_⟩
      have h : (w ∘ k.symm) ∘ k = w := by
        funext a
        exact congrArg w (k.symm_apply_apply a)
      funext x
      have he := baconPhysicalEncoding_mulVec (w ∘ k.symm) (e.symm x)
      change (baconPhysicalEncoding m b).mulVec w = v at hw
      rw [h, hw] at he
      change v (e.symm x) = (baconBinaryEncoding m b).mulVec (w ∘ k.symm) (e (e.symm x)) at he
      rw [Equiv.apply_symm_apply] at he
      exact he.symm
    · rintro ⟨w,hw⟩
      refine ⟨w ∘ k, ?_⟩
      funext x
      exact (baconPhysicalEncoding_mulVec w x).trans ((congrFun hw (e x)).trans (congrFun hv x))
  rw [hr, baconBinaryEncoding_range]
  constructor
  · rintro ⟨hX,hZ⟩
    constructor
    · intro a ha
      rw [← hv]
      funext x
      rw [physicalXWord_mulVec, shorXCheck_mulVec]
      exact hX a ha (e x)
    · intro z hz
      funext x
      rw [physicalZWord_mulVec]
      by_cases hx : ∀ i, rowParity (e x) i = rowParity (e x) 0
      · obtain ⟨r,hr,hzr⟩ := hz
        have he : maskDot (e x) z = 0 := by
          rw [hzr]
          simp only [maskDot, Fintype.sum_prod_type, repeatRows, ← Finset.sum_mul]
          change (∑ i, rowParity (e x) i * r i) = 0
          nth_rw 1 [show (∑ i, rowParity (e x) i * r i) = (∑ i, rowParity (e x) 0 * r i) by
            exact Finset.sum_congr rfl (fun i _ => congrArg (fun c => c * r i) (hx i))]
          rw [← Finset.mul_sum, hr, mul_zero]
        change (if maskDot (e x) z = 0 then (1 : ℂ) else -1) * v x = v x
        rw [he, ite_eq_left rfl, one_mul]
      · have hzv : v x = 0 := (congrFun hv x).symm.trans (hZ (e x) hx)
        rw [hzv, mul_zero]
  · rintro ⟨hX,hZ⟩
    constructor
    · intro a ha x
      have h := congrFun (hX a ha) (e.symm x)
      rw [← hv, physicalXWord_mulVec, shorXCheck_mulVec] at h
      change u (e (e.symm x)+a) = u (e (e.symm x)) at h
      simpa only [Equiv.apply_symm_apply] using h
    · intro x hx
      apply (shorZPairCheck_fixed_iff u).mp ?_ x
      · by_contra hn
        apply hx
        intro i
        by_contra hi
        exact hn ⟨i,0,hi⟩
      · intro i j
        funext y
        have h := congrFun (hZ _ (rowPair_is_centerZ (m := m) (b := b) i j)) (e.symm y)
        rw [← hv, physicalZPair_mulVec] at h
        change (shorZPairCheck i j).mulVec u (e (e.symm y)) = u (e (e.symm y)) at h
        simpa only [Equiv.apply_symm_apply] using h

#print axioms baconPhysicalEncoding_range_eq_center

end

end CriticalDepth.FaultShorSaturation.BaconShor
