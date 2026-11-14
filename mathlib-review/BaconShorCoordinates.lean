import FaultShorEncoding
import BaconShorBinaryGeometry

/-!
# Coordinates for the Bacon--Shor subsystem basis

The protected bit is the common row parity. Gauge coordinates are the
differences with the top row in the nonpivot columns. A final set of bits
varies the top row and parametrizes the X-center orbit.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open scoped BigOperators

variable {m b : ℕ}

abbrev Interior (m b : ℕ) := Fin m → Fin b → Bit
abbrev CenterCoordinate (b : ℕ) := Fin b → Bit
abbrev BaconMask (m b : ℕ) := Mask (m + 1) (b + 1)

def topBits (x : BaconMask m b) : CenterCoordinate b :=
  fun j => x (0, j.succ)

def gaugeBits (x : BaconMask m b) : Interior m b :=
  fun i j => x (i.succ, j.succ) - x (0, j.succ)

def baconWord (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b) : BaconMask m b :=
  parityWord ℓ (fun i j => Fin.cases (t j) (fun k => t j + u k j) i)

theorem baconWord_rowParity (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b)
    (i : Fin (m + 1)) : rowParity (baconWord ℓ u t) i = ℓ :=
  rowParity_parityWord _ _ _

theorem baconWord_topBits (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b) :
    topBits (baconWord ℓ u t) = t := rfl

theorem baconWord_gaugeBits (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b) :
    gaugeBits (baconWord ℓ u t) = u := by
  funext i j
  change t j + u i j - t j = u i j
  abel

/-- The full set of equal-row-parity words is parametrized without repetitions. -/
def baconWordEquiv : (Bit × (Interior m b × CenterCoordinate b)) ≃
    {x : BaconMask m b // ∀ i, rowParity x i = rowParity x 0} where
  toFun a := ⟨baconWord a.1 a.2.1 a.2.2,
    fun i => (baconWord_rowParity _ _ _ i).trans (baconWord_rowParity _ _ _ 0).symm⟩
  invFun x := (rowParity x.val 0, gaugeBits x.val, topBits x.val)
  left_inv a := by
    obtain ⟨ℓ, u, t⟩ := a
    change (rowParity (baconWord ℓ u t) 0, gaugeBits (baconWord ℓ u t),
      topBits (baconWord ℓ u t)) = (ℓ, u, t)
    rw [baconWord_rowParity, baconWord_gaugeBits, baconWord_topBits]
  right_inv x := by
    apply Subtype.ext
    change baconWord (rowParity x.val 0) (gaugeBits x.val) (topBits x.val) = x.val
    funext ij
    obtain ⟨i, j⟩ := ij
    have ht (a : Fin m) (p : Fin b) :
        topBits x.val p + gaugeBits x.val a p = x.val (a.succ, p.succ) := by
      change x.val (0, p.succ) + (x.val (a.succ, p.succ) - x.val (0, p.succ)) = _
      abel
    have hnp (a : Fin (m + 1)) (p : Fin b) :
        Fin.cases (topBits x.val p) (fun k => topBits x.val p + gaugeBits x.val k p) a =
          x.val (a, p.succ) := by
      refine Fin.cases rfl (fun k => ?_) a
      exact ht k p
    refine Fin.cases ?_ (fun p => ?_) j
    · have hrow := x.property i
      rw [rowParity, Fin.sum_univ_succ] at hrow
      change rowParity x.val 0 -
        (∑ p : Fin b, Fin.cases (topBits x.val p)
          (fun k => topBits x.val p + gaugeBits x.val k p) i) = x.val (i, 0)
      simp_rw [hnp]
      rw [← hrow, add_sub_cancel_right]
    · exact hnp i p

private theorem rowParity_add (x y : BaconMask m b) (i : Fin (m + 1)) :
    rowParity (x + y) i = rowParity x i + rowParity y i := by
  simp [rowParity, Pi.add_apply, Finset.sum_add_distrib]

theorem gaugeBits_add (x y : BaconMask m b) : gaugeBits (x + y) = gaugeBits x + gaugeBits y := by
  funext i j
  change (x (i.succ, j.succ) + y (i.succ, j.succ)) -
      (x (0, j.succ) + y (0, j.succ)) =
    (x (i.succ, j.succ) - x (0, j.succ)) + (y (i.succ, j.succ) - y (0, j.succ))
  abel

/-- Translation by a gauge X mask updates the gauge and center coordinates. -/
theorem baconWord_add_gaugeX (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b)
    (a : BaconMask m b) (ha : gaugeX a) :
    baconWord ℓ u t + a = baconWord ℓ (u + gaugeBits a) (t + topBits a) := by
  let y := baconWord ℓ u t + a
  have hp (i) : rowParity y i = ℓ := by
    change rowParity (baconWord ℓ u t + a) i = ℓ
    rw [rowParity_add, baconWord_rowParity, ha i, add_zero]
  have hh := congrArg Subtype.val ((baconWordEquiv (m := m) (b := b)).apply_symm_apply
    ⟨y, fun i => (hp i).trans (hp 0).symm⟩)
  change baconWord (rowParity y 0) (gaugeBits y) (topBits y) = y at hh
  have hu : gaugeBits y = u + gaugeBits a := by
    change gaugeBits (baconWord ℓ u t + a) = _
    rw [gaugeBits_add, baconWord_gaugeBits]
  rw [hp, hu] at hh
  exact hh.symm

/-- The full pivot-column X flips the protected bit and preserves gauge coordinates. -/
theorem baconWord_add_bareX (ℓ : Bit) (u : Interior m b) (t : CenterCoordinate b) :
    baconWord ℓ u t + fullXColumn (rows := m + 1) 0 = baconWord (ℓ + 1) u t := by
  let a : BaconMask m b := fullXColumn 0
  let y := baconWord ℓ u t + a
  have ha (i : Fin (m + 1)) : rowParity a i = 1 := by
    simp [a, rowParity, fullXColumn, Finset.sum_ite_eq']
  have hp (i) : rowParity y i = ℓ + 1 := by
    change rowParity (baconWord ℓ u t + a) i = _
    rw [rowParity_add, baconWord_rowParity, ha]
  have hga : gaugeBits a = 0 := by
    funext i j
    simp [a, gaugeBits, fullXColumn, Fin.succ_ne_zero]
  have hta : topBits a = 0 := by
    funext j
    simp [a, topBits, fullXColumn, Fin.succ_ne_zero]
  have hh := congrArg Subtype.val ((baconWordEquiv (m := m) (b := b)).apply_symm_apply
    ⟨y, fun i => (hp i).trans (hp 0).symm⟩)
  change baconWord (rowParity y 0) (gaugeBits y) (topBits y) = y at hh
  have hu : gaugeBits y = u := by
    change gaugeBits (baconWord ℓ u t + a) = _
    rw [gaugeBits_add, baconWord_gaugeBits, hga, add_zero]
  have ht : topBits y = t := by
    change topBits (baconWord ℓ u t) + topBits a = _
    rw [baconWord_topBits, hta, add_zero]
  rw [hp, hu, ht] at hh
  exact hh.symm

#print axioms baconWordEquiv
#print axioms baconWord_add_gaugeX
#print axioms baconWord_add_bareX

end CriticalDepth.FaultShorSaturation.BaconShor
