import BaconShorCoordinates

/-!
# Adjacent-pair generators for the Bacon--Shor gauge masks

The horizontal XX pairs generate all even binary rows. Transposition
gives the vertical ZZ generation statement with the same physical labels.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open scoped BigOperators

variable {m b : ℕ}

/-- The two sites in one horizontal edge of the physical rectangle. -/
def horizontalPair (i : Fin (m+1)) (j : Fin b) : BaconMask m b :=
  Pi.single (i,j.castSucc) 1 + Pi.single (i,j.succ) 1

/-- The two sites in one vertical edge of the physical rectangle. -/
def verticalPair (i : Fin m) (j : Fin (b+1)) : BaconMask m b :=
  transpose (horizontalPair j i : BaconMask b m)

private def evenRows (m b : ℕ) : Submodule Bit (BaconMask m b) where
  carrier := {a | gaugeX a}
  zero_mem' := by intro i; simp [rowParity]
  add_mem' := by
    intro x y hx hy i
    change rowParity (x+y) i = 0
    have h : rowParity (x+y) i = rowParity x i + rowParity y i := by
      simp [rowParity, Pi.add_apply, Finset.sum_add_distrib]
    rw [h, hx i, hy i, add_zero]
  smul_mem' := by
    intro r a ha i
    change rowParity (r • a) i = 0
    have h : rowParity (r • a) i = r * rowParity a i := by
      simp [rowParity, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [h, ha i, mul_zero]

private def horizontalSpan (m b : ℕ) : Submodule Bit (BaconMask m b) :=
  Submodule.span Bit (Set.range (fun x : Fin (m+1) × Fin b => horizontalPair x.1 x.2))

private theorem bit_add_self (a : Bit) : a + a = 0 := by decide +revert

private theorem horizontalPair_even (i : Fin (m+1)) (j : Fin b) :
    gaugeX (horizontalPair i j) := by
  intro r
  by_cases h : i = r
  · subst r
    simp [rowParity, horizontalPair, Pi.single_apply, Finset.sum_add_distrib,
      Finset.sum_ite_eq', bit_add_self]
  · simp [rowParity, horizontalPair, Pi.single_apply, h, Ne.symm h]

private theorem pivotPair_mem (i : Fin (m+1)) (j : Fin (b+1)) :
    Pi.single (i,(0 : Fin (b+1))) 1 + Pi.single (i,j) 1 ∈ horizontalSpan m b := by
  induction j using Fin.induction with
  | zero =>
    have h : (Pi.single (i,(0 : Fin (b+1))) 1 : BaconMask m b) +
        Pi.single (i,(0 : Fin (b+1))) 1 = 0 := by
      funext x
      exact bit_add_self _
    rw [h]
    exact (horizontalSpan m b).zero_mem
  | succ j ih =>
    have hstep : horizontalPair i j ∈ horizontalSpan m b :=
      Submodule.subset_span ⟨(i,j),rfl⟩
    have heq :
        (Pi.single (i,(0 : Fin (b+1))) 1 + Pi.single (i,j.castSucc) 1 : BaconMask m b) +
            horizontalPair i j =
          Pi.single (i,(0 : Fin (b+1))) 1 + Pi.single (i,j.succ) 1 := by
      unfold horizontalPair
      funext x
      let A : BaconMask m b := Pi.single (i, (0 : Fin (b+1))) 1
      let B : BaconMask m b := Pi.single (i,j.castSucc) 1
      let C : BaconMask m b := Pi.single (i,j.succ) 1
      change (A x + B x) + (B x + C x) = A x + C x
      rw [← add_assoc (A x + B x), add_assoc (A x), bit_add_self, add_zero]
    exact heq ▸ (horizontalSpan m b).add_mem ih hstep

private theorem expand_evenRows (x : BaconMask m b) (hx : gaugeX x) :
    x = ∑ i : Fin (m+1), ∑ j : Fin b,
      x (i,j.succ) • (Pi.single (i,(0 : Fin (b+1))) 1 + Pi.single (i,j.succ) 1) := by
  classical
  funext ij
  obtain ⟨i,k⟩ := ij
  have hrow (r : Fin (m+1)) (c : Fin (b+1)) :
      (∑ j : Fin b,
        x (r,j.succ) * ((Pi.single (r,(0 : Fin (b+1))) 1 : BaconMask m b) (i,c) +
          (Pi.single (r,j.succ) 1 : BaconMask m b) (i,c))) =
        if i = r then
          (∑ j : Fin b, x (r,j.succ) *
            ((if c = 0 then 1 else 0) + if c = j.succ then 1 else 0))
        else 0 := by
    by_cases h : i = r <;> simp [Pi.single_apply, Prod.mk.injEq, h, eq_comm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, hrow, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  refine Fin.cases ?_ (fun j => ?_) k
  · have hp := hx i
    rw [rowParity, Fin.sum_univ_succ] at hp
    have hm : x (i,0) + ∑ j : Fin b, x (i,j.succ) = 0 := hp
    have h := congrArg (fun t : Bit => x (i,0) + t) hm
    have hs : (∑ j : Fin b, x (i,j.succ)) = x (i,0) := by
      simpa only [← add_assoc, bit_add_self, zero_add, add_zero] using h
    simpa [Ne.symm (Fin.succ_ne_zero _)] using hs.symm
  · simp [Fin.succ_ne_zero, Finset.sum_ite_eq', mul_ite]

theorem gaugeX_iff_horizontalSpan (x : BaconMask m b) :
    gaugeX x ↔ x ∈ Submodule.span Bit (Set.range
      (fun p : Fin (m+1) × Fin b => horizontalPair p.1 p.2)) := by
  change gaugeX x ↔ x ∈ horizontalSpan m b
  constructor
  · intro hx
    rw [expand_evenRows x hx]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    exact (horizontalSpan m b).smul_mem _ (pivotPair_mem i j.succ)
  · intro hx
    have hle : horizontalSpan m b ≤ evenRows m b := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,j⟩,rfl⟩
      exact horizontalPair_even i j
    exact hle hx

private def transposeLinear (m b : ℕ) : BaconMask m b →ₗ[Bit] BaconMask b m where
  toFun := transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem gaugeZ_iff_verticalSpan (z : BaconMask m b) :
    gaugeZ z ↔ z ∈ Submodule.span Bit (Set.range
      (fun p : Fin m × Fin (b+1) => verticalPair p.1 p.2)) := by
  have hs : Set.range (fun p : Fin m × Fin (b+1) => verticalPair p.1 p.2) =
      transposeLinear b m '' Set.range
        (fun p : Fin (b+1) × Fin m => horizontalPair p.1 p.2) := by
    ext u
    constructor
    · rintro ⟨⟨i,j⟩,rfl⟩
      exact ⟨horizontalPair j i, ⟨(j,i),rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨j,i⟩,rfl⟩,rfl⟩
      exact ⟨(i,j),rfl⟩
  rw [hs, ← Submodule.map_span]
  constructor
  · intro hz
    refine ⟨transpose z, (gaugeX_iff_horizontalSpan _).mp hz, ?_⟩
    exact transpose_transpose z
  · rintro ⟨x,hx,rfl⟩
    change gaugeX (transpose (transpose x))
    rw [transpose_transpose]
    exact (gaugeX_iff_horizontalSpan _).mpr hx

theorem centerX_iff_adjacentGaugeCenter (x : BaconMask m b) :
    centerX x ↔
      x ∈ Submodule.span Bit (Set.range (fun p : Fin (m+1) × Fin b => horizontalPair p.1 p.2)) ∧
      ∀ z ∈ Submodule.span Bit (Set.range (fun p : Fin m × Fin (b+1) => verticalPair p.1 p.2)),
        maskDot x z = 0 := by
  rw [centerX_iff x 0, ← gaugeX_iff_horizontalSpan]
  constructor
  · rintro ⟨hX,hcols⟩
    have hbare := (bareCentralizes_iff x 0).mpr ⟨hcols, by intros; rfl⟩
    exact ⟨hX, fun z hz => hbare.2 z ((gaugeZ_iff_verticalSpan z).mpr hz)⟩
  · rintro ⟨hX,hz⟩
    have hbare : bareCentralizes x 0 :=
      ⟨fun _ _ => by simp [maskDot], fun z hz' => hz z ((gaugeZ_iff_verticalSpan z).mp hz')⟩
    exact ⟨hX, ((bareCentralizes_iff x 0).mp hbare).1⟩

theorem centerZ_iff_adjacentGaugeCenter (z : BaconMask m b) :
    centerZ z ↔
      z ∈ Submodule.span Bit (Set.range (fun p : Fin m × Fin (b+1) => verticalPair p.1 p.2)) ∧
      ∀ x ∈ Submodule.span Bit (Set.range (fun p : Fin (m+1) × Fin b => horizontalPair p.1 p.2)),
        maskDot z x = 0 := by
  rw [centerZ_iff z 0, ← gaugeZ_iff_verticalSpan]
  constructor
  · rintro ⟨hZ,hrows⟩
    have hbare := (bareCentralizes_iff 0 z).mpr ⟨by intros; rfl, hrows⟩
    exact ⟨hZ, fun x hx => hbare.1 x ((gaugeX_iff_horizontalSpan x).mpr hx)⟩
  · rintro ⟨hZ,hx⟩
    have hbare : bareCentralizes 0 z :=
      ⟨fun x hx' => hx x ((gaugeX_iff_horizontalSpan x).mp hx'), fun _ _ => by simp [maskDot]⟩
    exact ⟨hZ, ((bareCentralizes_iff 0 z).mp hbare).2⟩


#print axioms gaugeX_iff_horizontalSpan
#print axioms gaugeZ_iff_verticalSpan
#print axioms centerX_iff_adjacentGaugeCenter
#print axioms centerZ_iff_adjacentGaugeCenter

end CriticalDepth.FaultShorSaturation.BaconShor
