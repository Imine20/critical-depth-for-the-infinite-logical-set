import BaconShorSubsystemEncoding

/-!
# Binary gauge actions on the Bacon--Shor code columns

A gauge X translates the gauge coordinate. A gauge Z has a phase
depending only on this gauge coordinate. Neither depends on the
protected bit, and changing the center-orbit coordinate leaves both
statements valid.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open scoped BigOperators

variable {m b : ℕ}

private theorem bit_add_self (x : Bit) : x + x = 0 := by decide +revert

private theorem mask_add_self (x : BaconMask m b) : x + x = 0 := by
  funext i
  exact bit_add_self (x i)

private theorem gauge_add_self (x : Interior m b) : x + x = 0 := by
  funext i j
  exact bit_add_self (x i j)

private theorem orbitWords_translate_gauge (a : BaconMask m b) (ha : gaugeX a)
    (x : BaconMask m b) (ℓ : Bit) (u : Interior m b) :
    x + a ∈ orbitWords ℓ u ↔ x ∈ orbitWords ℓ (u + gaugeBits a) := by
  rw [orbitWords_mem, orbitWords_mem]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t + topBits a, ?_⟩
    rw [← baconWord_add_gaugeX ℓ u t a ha, ht, add_assoc, mask_add_self, add_zero]
  · rintro ⟨t, ht⟩
    refine ⟨t + topBits a, ?_⟩
    rw [← ht, baconWord_add_gaugeX ℓ (u + gaugeBits a) t a ha,
      add_assoc u, gauge_add_self, add_zero]

theorem baconBinaryEncoding_gaugeX (a : BaconMask m b) (ha : gaugeX a)
    (x : BaconMask m b) (ℓ : Bit) (u : Interior m b) :
    baconBinaryEncoding m b (x + a) (ℓ, u) =
      baconBinaryEncoding m b x (ℓ, u + gaugeBits a) := by
  simp only [baconBinaryEncoding, orbitWords_translate_gauge a ha]

private theorem baconWord_decomposition (ℓ : Bit) (u : Interior m b)
    (t : CenterCoordinate b) :
    baconWord ℓ u t = baconWord 0 u 0 + baconWord ℓ 0 t := by
  funext ij
  rcases ij with ⟨i,j⟩
  have hentry (j : Fin b) :
      Fin.cases (motive := fun _ => Bit) (t j) (fun k => t j + u k j) i =
        Fin.cases (motive := fun _ => Bit) 0 (fun k => u k j) i + t j := by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp [add_comm]
  refine Fin.cases ?_ (fun j => ?_) j
  · change (ℓ - ∑ j : Fin b, Fin.cases (motive := fun _ => Bit) (t j) (fun k => t j + u k j) i) =
      (0 - ∑ j : Fin b, Fin.cases (motive := fun _ => Bit) 0 (fun k => 0 + u k j) i) +
      (ℓ - ∑ j : Fin b, Fin.cases (motive := fun _ => Bit) (t j) (fun k => t j + 0) i)
    have hU (j : Fin b) : Fin.cases (motive := fun _ => Bit) 0 (fun k => 0 + u k j) i =
        Fin.cases (motive := fun _ => Bit) 0 (fun k => u k j) i := by
      refine Fin.cases rfl (fun k => ?_) i
      exact zero_add _
    have hT (j : Fin b) : Fin.cases (motive := fun _ => Bit) (t j) (fun _ : Fin m => t j + 0) i = t j := by
      refine Fin.cases rfl (fun _ => ?_) i
      exact add_zero _
    simp_rw [hentry, hU, hT, Finset.sum_add_distrib]
    abel
  · change Fin.cases (motive := fun _ => Bit) (t j) (fun k => t j + u k j) i =
      Fin.cases (motive := fun _ => Bit) 0 (fun k => 0 + u k j) i + Fin.cases (motive := fun _ => Bit) (t j) (fun k => t j + 0) i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp [add_comm]

private theorem baconWord_zeroGauge_constantColumn (ℓ : Bit) (t : CenterCoordinate b)
    (i k : Fin (m + 1)) (j : Fin (b + 1)) :
    baconWord ℓ (0 : Interior m b) t (i,j) = baconWord ℓ 0 t (k,j) := by
  have hConst (a : Fin (m + 1)) (j : Fin b) :
      Fin.cases (motive := fun _ => Bit) (t j) (fun _ : Fin m => t j + 0) a = t j := by
    refine Fin.cases rfl (fun _ => add_zero _) a
  refine Fin.cases ?_ (fun j => ?_) j
  · change (ℓ - ∑ j : Fin b, Fin.cases (motive := fun _ => Bit) (t j) (fun _ : Fin m => t j + 0) i) =
      (ℓ - ∑ j : Fin b, Fin.cases (motive := fun _ => Bit) (t j) (fun _ : Fin m => t j + 0) k)
    simp_rw [hConst]
  · exact (hConst i j).trans (hConst k j).symm

private theorem dot_constantColumns_gaugeZ (x z : BaconMask m b)
    (hx : ∀ i k j, x (i,j) = x (k,j)) (hz : gaugeZ z) :
    maskDot x z = 0 := by
  rw [← dot_transpose]
  simp only [maskDot, Fintype.sum_prod_type, transpose]
  apply Finset.sum_eq_zero
  intro j _
  have he : (∑ i : Fin (m + 1), x (i,j) * z (i,j)) =
      x (0,j) * rowParity (transpose z) j := by
    rw [rowParity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hx k 0]
    rfl
  rw [he, hz j, mul_zero]

theorem baconWord_dot_gaugeZ (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b)
    (z : BaconMask m b) (hz : gaugeZ z) :
    maskDot (baconWord ℓ u t) z = maskDot (baconWord 0 u 0) z := by
  have hAdd (x y : BaconMask m b) :
      maskDot (x + y) z = maskDot x z + maskDot y z := by
    simp [maskDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [baconWord_decomposition, hAdd,
    dot_constantColumns_gaugeZ _ z (baconWord_zeroGauge_constantColumn ℓ t) hz, add_zero]

#print axioms baconBinaryEncoding_gaugeX
#print axioms baconWord_dot_gaugeZ

end CriticalDepth.FaultShorSaturation.BaconShor
