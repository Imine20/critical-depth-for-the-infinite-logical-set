import CSSPhaseDifferences

/-!
# Quadratic reconstruction of a binary phase

Constant mixed coordinate differences determine a quadratic phase.
The linear factors are the single-coordinate differences at zero.
-/

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

variable {ι G : Type*} [DecidableEq ι] [CommGroup G]

private abbrev coordinateWord (i : ι) : BinaryWord ι := Pi.single i 1

/-- The multiplicative difference in one binary coordinate. -/
def bitPhaseDifference (u : BinaryWord ι → G) (i : ι) :
    BinaryWord ι → G :=
  phaseDifference (coordinateWord i) u

/-- The multiplicative difference in two binary coordinates. -/
def mixedBitPhaseDifference (u : BinaryWord ι → G) (i j : ι) :
    BinaryWord ι → G :=
  bitPhaseDifference (bitPhaseDifference u j) i

theorem mixedBitPhaseDifference_comm (u : BinaryWord ι → G)
    (i j : ι) (x : BinaryWord ι) :
    mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u j i x :=
  phaseDifference_comm (coordinateWord i) (coordinateWord j) u x

theorem mixedBitPhaseDifference_square_eq_one (u : BinaryWord ι → G)
    (i j : ι)
    (h : ∀ x, mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0) :
    mixedBitPhaseDifference u i j 0 * mixedBitPhaseDifference u i j 0 = 1 :=
  square_eq_one_of_constant_phaseDifference (ZModModule.add_self (coordinateWord i))
    (bitPhaseDifference u j) _ h

private theorem bitPhaseDifference_sum (u : BinaryWord ι → G)
    (h : ∀ i j, i ≠ j → ∀ x,
      mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0)
    (a : ι) (s : Finset ι) (ha : a ∉ s) :
    bitPhaseDifference u a (∑ i ∈ s, coordinateWord i) =
      bitPhaseDifference u a 0 * ∏ i ∈ s, mixedBitPhaseDifference u i a 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hia : i ≠ a := by
      intro hEq
      exact ha (hEq ▸ Finset.mem_insert_self i s)
    have has : a ∉ s := fun hs => ha (Finset.mem_insert_of_mem hs)
    have hshift := h i a hia (∑ j ∈ s, coordinateWord j)
    change bitPhaseDifference u a ((∑ j ∈ s, coordinateWord j) + coordinateWord i) /
        bitPhaseDifference u a (∑ j ∈ s, coordinateWord j) =
          mixedBitPhaseDifference u i a 0 at hshift
    rw [Finset.sum_insert hi, add_comm (coordinateWord i), div_eq_iff_eq_mul'.mp hshift,
      ih has, Finset.prod_insert hi]
    ac_rfl

section Reconstruction

variable [Fintype ι] [LinearOrder ι]

/-- The product of the linear factors and the factors for all active
unordered pairs reconstructs the phase from its derivatives at zero. -/
theorem phase_eq_quadratic_product (u : BinaryWord ι → G)
    (h : ∀ i j, i ≠ j → ∀ x,
      mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0)
    (x : BinaryWord ι) :
    u x = u 0 * (∏ i ∈ binaryWordSupport x, bitPhaseDifference u i 0) *
      ∏ i ∈ binaryWordSupport x, ∏ j ∈ (binaryWordSupport x).filter (· < i),
        mixedBitPhaseDifference u j i 0 := by
  have hsum (s : Finset ι) :
      u (∑ i ∈ s, coordinateWord i) =
        u 0 * (∏ i ∈ s, bitPhaseDifference u i 0) *
          ∏ i ∈ s, ∏ j ∈ s.filter (· < i), mixedBitPhaseDifference u j i 0 := by
    refine Finset.induction_on_max s (by simp) ?_
    intro a s hlt ih
    have ha : a ∉ s := fun hm => (lt_irrefl a) (hlt a hm)
    have hfilter : (insert a s).filter (· < a) = s := by
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl a)]
      exact Finset.filter_eq_self.mpr hlt
    have hOld :
        (∏ i ∈ s, ∏ j ∈ (insert a s).filter (· < i), mixedBitPhaseDifference u j i 0) =
          ∏ i ∈ s, ∏ j ∈ s.filter (· < i), mixedBitPhaseDifference u j i 0 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.filter_insert, ite_eq_right (not_lt_of_ge (hlt i hi).le)]
    have hNew :
        (∏ i ∈ insert a s, ∏ j ∈ (insert a s).filter (· < i),
          mixedBitPhaseDifference u j i 0) =
        (∏ j ∈ s, mixedBitPhaseDifference u j a 0) *
          ∏ i ∈ s, ∏ j ∈ s.filter (· < i), mixedBitPhaseDifference u j i 0 := by
      rw [Finset.prod_insert ha, hfilter, hOld]
    have hstep :
        u ((∑ i ∈ s, coordinateWord i) + coordinateWord a) =
          u (∑ i ∈ s, coordinateWord i) *
            bitPhaseDifference u a (∑ i ∈ s, coordinateWord i) :=
      (mul_div_cancel _ _).symm
    rw [Finset.sum_insert ha, add_comm (coordinateWord a), hstep, ih,
      bitPhaseDifference_sum u h a s ha, hNew, Finset.prod_insert ha]
    ac_rfl
  have hs := hsum (binaryWordSupport x)
  rw [show (∑ i ∈ binaryWordSupport x, coordinateWord i) = x from
    sum_basis_on_binaryWordSupport x] at hs
  exact hs

end Reconstruction

/-- The complex sign for a binary exponent. -/
noncomputable def binaryPhaseSign (a : ZMod 2) : ℂˣ :=
  if a = 0 then 1 else Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)

@[simp] theorem binaryPhaseSign_zero : binaryPhaseSign 0 = 1 := by
  simp [binaryPhaseSign]

theorem binaryPhaseSign_one :
    binaryPhaseSign 1 = Units.mk0 (-1 : ℂ) (neg_ne_zero.mpr one_ne_zero) := by
  simp [binaryPhaseSign]

private theorem binary_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have hv := a.val_lt
    have hz : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
    exact (ZMod.val_eq_one (by decide) a).mp (by omega)

private theorem binaryPhaseSign_add (a b : ZMod 2) :
    binaryPhaseSign (a + b) = binaryPhaseSign a * binaryPhaseSign b := by
  rcases binary_eq_zero_or_one a with rfl | rfl
  · simp
  rcases binary_eq_zero_or_one b with rfl | rfl
  · simp
  rw [show (1 + 1 : ZMod 2) = 0 by decide, binaryPhaseSign_zero, binaryPhaseSign_one]
  apply Units.ext
  simp [Units.val_mul]

private theorem binaryPhaseSign_sum {κ : Type*} (s : Finset κ) (f : κ → ZMod 2) :
    binaryPhaseSign (∑ i ∈ s, f i) = ∏ i ∈ s, binaryPhaseSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, binaryPhaseSign_add, ih]

/-- The off-diagonal entry records the nontrivial mixed sign in that pair. -/
noncomputable def mixedPhaseMatrix (u : BinaryWord ι → ℂˣ) : Matrix ι ι (ZMod 2) := by
  classical
  exact fun i j => if i = j ∨ mixedBitPhaseDifference u i j 0 = 1 then 0 else 1

@[simp] theorem mixedPhaseMatrix_diag (u : BinaryWord ι → ℂˣ) (i : ι) :
    mixedPhaseMatrix u i i = 0 := by
  classical
  simp [mixedPhaseMatrix]

theorem mixedPhaseMatrix_isSymm (u : BinaryWord ι → ℂˣ) :
    (mixedPhaseMatrix u).IsSymm := by
  classical
  ext i j
  change mixedPhaseMatrix u j i = mixedPhaseMatrix u i j
  by_cases hij : j = i
  · subst j
    rfl
  · have hji : i ≠ j := Ne.symm hij
    simp only [mixedPhaseMatrix, hij, hji, false_or,
      mixedBitPhaseDifference_comm u j i 0]

theorem mixedPhaseMatrix_eq_zero_iff (u : BinaryWord ι → ℂˣ)
    (i j : ι) (hij : i ≠ j) :
    mixedPhaseMatrix u i j = 0 ↔ mixedBitPhaseDifference u i j 0 = 1 := by
  classical
  by_cases h : mixedBitPhaseDifference u i j 0 = 1 <;>
    simp [mixedPhaseMatrix, hij, h]

private theorem binaryPhaseSign_mixedPhaseMatrix (u : BinaryWord ι → ℂˣ)
    (i j : ι) (hij : i ≠ j)
    (h : ∀ x, mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0) :
    binaryPhaseSign (mixedPhaseMatrix u i j) = mixedBitPhaseDifference u i j 0 := by
  classical
  let c := mixedBitPhaseDifference u i j 0
  have hsq : c * c = 1 := mixedBitPhaseDifference_square_eq_one u i j h
  have hsq' : (c : ℂ) * (c : ℂ) = 1 := by
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hsq
  rcases mul_self_eq_one_iff.mp hsq' with hc | hc
  · have hOne : c = 1 := Units.ext hc
    change binaryPhaseSign (mixedPhaseMatrix u i j) = c
    rw [(mixedPhaseMatrix_eq_zero_iff u i j hij).mpr hOne, binaryPhaseSign_zero, hOne]
  · have hNeg : c = Units.mk0 (-1 : ℂ) (neg_ne_zero.mpr one_ne_zero) := Units.ext hc
    have hne : c ≠ 1 := by
      intro hh
      have hh' : (c : ℂ) = 1 := congrArg (fun z : ℂˣ => (z : ℂ)) hh
      exact (neg_ne_self.mpr (one_ne_zero : (1 : ℂ) ≠ 0)) (hc.symm.trans hh')
    have hQ : mixedPhaseMatrix u i j = 1 := by
      simp [mixedPhaseMatrix, hij, show mixedBitPhaseDifference u i j 0 ≠ 1 from hne]
    change binaryPhaseSign (mixedPhaseMatrix u i j) = c
    rw [hQ, binaryPhaseSign_one, hNeg]

variable [Fintype ι] [LinearOrder ι]

/-- The multilinear quadratic polynomial over the binary field obtained
by choosing one of the two orders for each off-diagonal pair. -/
def quadraticPhaseParity (Q : Matrix ι ι (ZMod 2)) (x : BinaryWord ι) : ZMod 2 :=
  ∑ i, ∑ j ∈ Finset.univ.filter (· < i), Q j i * x j * x i

omit [DecidableEq ι] in
private theorem quadraticPhaseParity_eq_support (Q : Matrix ι ι (ZMod 2))
    (x : BinaryWord ι) :
    quadraticPhaseParity Q x =
      ∑ i ∈ binaryWordSupport x, ∑ j ∈ (binaryWordSupport x).filter (· < i), Q j i := by
  classical
  unfold quadraticPhaseParity
  symm
  calc
    _ = ∑ i ∈ binaryWordSupport x, ∑ j ∈ Finset.univ.filter (· < i),
          Q j i * x j * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hxi : x i = 1 := (binary_eq_zero_or_one (x i)).resolve_left
        (Finset.mem_filter.mp hi).2
      rw [hxi]
      simp only [mul_one]
      calc
        _ = ∑ j ∈ (binaryWordSupport x).filter (· < i), Q j i * x j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hxj : x j = 1 := (binary_eq_zero_or_one (x j)).resolve_left
            (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
          rw [hxj, mul_one]
        _ = _ := by
          apply Finset.sum_subset (Finset.filter_subset_filter _ (Finset.subset_univ _))
          intro j hj hnot
          have hxj : x j = 0 := by
            by_contra hn
            exact hnot (Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩, (Finset.mem_filter.mp hj).2⟩)
          rw [hxj, mul_zero]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hxi : x i = 0 := by simpa [binaryWordSupport] using hi
      simp [hxi]

/-- A nonvanishing complex phase with constant mixed coordinate differences
is its constant value times a product of linear phases and the sign of a
multilinear quadratic binary polynomial. The matrix is symmetric with zero
diagonal, and its nonzero entries are exactly the nontrivial mixed pairs. -/
theorem phase_eq_quadratic_parity (u : BinaryWord ι → ℂˣ)
    (h : ∀ i j, i ≠ j → ∀ x,
      mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0)
    (x : BinaryWord ι) :
    u x = u 0 * (∏ i ∈ binaryWordSupport x, bitPhaseDifference u i 0) *
      binaryPhaseSign (quadraticPhaseParity (mixedPhaseMatrix u) x) := by
  rw [phase_eq_quadratic_product u h x, quadraticPhaseParity_eq_support,
    binaryPhaseSign_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [binaryPhaseSign_sum]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := ne_of_lt (Finset.mem_filter.mp hj).2
  exact (binaryPhaseSign_mixedPhaseMatrix u j i hji (h j i hji)).symm

#print axioms phase_eq_quadratic_product
#print axioms phase_eq_quadratic_parity
#print axioms mixedPhaseMatrix_isSymm
#print axioms mixedPhaseMatrix_eq_zero_iff

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
