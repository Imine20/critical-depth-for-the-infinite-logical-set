import FaultHaarSphere

/-!
The real coordinate fourth moments of spherical Haar probability follow
from sign changes, coordinate permutations and a planar forty-five-degree
orthogonal transformation.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open MeasureTheory Matrix Metric WithLp
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev RealSphere (ι : Type*) [Fintype ι] := UnitSphere (EuclideanSpace ℝ ι)

abbrev realCoordinate (x : RealSphere ι) (i : ι) : ℝ := x.val i

private theorem realCoordinate_continuous (i : ι) :
    Continuous (fun x : RealSphere ι => realCoordinate x i) :=
  (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp continuous_subtype_val

private theorem realSphere_sum_sq (x : RealSphere ι) :
    ∑ i, realCoordinate x i ^ 2 = 1 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x.val
  rw [mem_sphere_zero_iff_norm.mp x.property] at h
  simpa [Real.norm_eq_abs, sq_abs] using h.symm

private def signFlip (i : ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toLinearEquiv :=
    { toFun := fun x => toLp 2 (fun j => if j = i then -(x j) else x j)
      invFun := fun x => toLp 2 (fun j => if j = i then -(x j) else x j)
      left_inv := by
        intro x
        ext j
        by_cases h : j = i <;> simp [PiLp.toLp_apply, h]
      right_inv := by
        intro x
        ext j
        by_cases h : j = i <;> simp [PiLp.toLp_apply, h]
      map_add' := by
        intro x y
        ext j
        by_cases h : j = i <;> simp [PiLp.add_apply, h, add_comm]
      map_smul' := by
        intro c x
        ext j
        by_cases h : j = i <;> simp [PiLp.toLp_apply, PiLp.smul_apply, h] }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j _
    change ‖if j = i then -(x j) else x j‖ ^ 2 = _
    by_cases h : j = i <;> simp [h]

private theorem signFlip_apply (i j : ι) (x : RealSphere ι) :
    realCoordinate (sphereAction (signFlip i) x) j =
      if j = i then -realCoordinate x j else realCoordinate x j := rfl

private def reflectPair (i j : ι) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  toLp 2 fun k => if k = i then Real.sqrt (1/2) * (x i + x j)
    else if k = j then Real.sqrt (1/2) * (x i - x j) else x k

private theorem reflectPair_apply (i j k : ι) (x : EuclideanSpace ℝ ι) :
    reflectPair i j x k = if k = i then Real.sqrt (1/2) * (x i + x j)
      else if k = j then Real.sqrt (1/2) * (x i - x j) else x k := rfl

private theorem reflectionFactor_sq : (Real.sqrt (1 / 2)) ^ 2 = (1 / 2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem reflectPair_involution (i j : ι) (hij : i ≠ j) :
    Function.Involutive (reflectPair i j) := by
  intro x
  ext k
  simp only [reflectPair_apply]
  by_cases hki : k = i
  · subst k
    simp only [ite_true, if_neg hij, if_neg (Ne.symm hij)]
    nlinarith only [reflectionFactor_sq, congrArg (fun w : ℝ => w * x i) reflectionFactor_sq]
  · by_cases hkj : k = j
    · subst k
      simp only [ite_true, if_neg hij, if_neg (Ne.symm hij)]
      nlinarith only [reflectionFactor_sq, congrArg (fun w : ℝ => w * x j) reflectionFactor_sq]
    · simp [hki, hkj]

private theorem twoCoordinate_add_erase (f : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∑ k, f k) = (∑ k ∈ (Finset.univ.erase i).erase j, f k) + f j + f i := by
  rw [Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩),
    Finset.sum_erase_add _ _ (Finset.mem_univ i)]

private def reflectPairIsometry (i j : ι) (hij : i ≠ j) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toLinearEquiv :=
    { toFun := reflectPair i j
      invFun := reflectPair i j
      left_inv := reflectPair_involution i j hij
      right_inv := reflectPair_involution i j hij
      map_add' := by
        intro x y
        ext k
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp only [reflectPair_apply, PiLp.add_apply, hki, hkj, hij, Ne.symm hij, ite_true, ite_false] <;> ring
      map_smul' := by
        intro c x
        ext k
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp only [reflectPair_apply, PiLp.smul_apply, smul_eq_mul,
            hki, hkj, hij, Ne.symm hij, ite_true, ite_false, RingHom.id_apply] <;> ring }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [twoCoordinate_add_erase _ hij, twoCoordinate_add_erase _ hij]
    have hrest :
        (∑ k ∈ (Finset.univ.erase i).erase j, reflectPair i j x k ^ 2) =
          ∑ k ∈ (Finset.univ.erase i).erase j, x k ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp [reflectPair_apply, hki, hkj]
    change (∑ k ∈ (Finset.univ.erase i).erase j, reflectPair i j x k ^ 2) +
        reflectPair i j x j ^ 2 + reflectPair i j x i ^ 2 =
      (∑ k ∈ (Finset.univ.erase i).erase j, x k ^ 2) + x j ^ 2 + x i ^ 2
    rw [hrest, reflectPair_apply, reflectPair_apply]
    simp only [ite_true, if_neg (Ne.symm hij), mul_pow, reflectionFactor_sq]
    ring

private theorem reflectPairIsometry_apply_left (i j : ι) (hij : i ≠ j) (x : RealSphere ι) :
    realCoordinate (sphereAction (reflectPairIsometry i j hij) x) i =
      Real.sqrt (1/2) * (realCoordinate x i + realCoordinate x j) := by
  change reflectPair i j x.val i = _
  simp [reflectPair_apply]

abbrev realSphereIntegral (f : RealSphere ι → ℝ) : ℝ :=
  ∫ x, f x ∂sphereHaar (EuclideanSpace ℝ ι)

private theorem realSphereIntegral_congr {f g : RealSphere ι → ℝ} (h : ∀ x, f x = g x) :
    realSphereIntegral f = realSphereIntegral g := congrArg realSphereIntegral (funext h)

private theorem integral_odd_signFlip_zero (i : ι) (f : RealSphere ι → ℝ)
    (h : ∀ x, f (sphereAction (signFlip i) x) = -f x) :
    realSphereIntegral f = 0 := by
  have hs := integral_sphereAction (signFlip i) f
  have he := realSphereIntegral_congr h
  change realSphereIntegral (fun x => f (sphereAction (signFlip i) x)) = _ at hs
  rw [hs] at he
  change realSphereIntegral f = (∫ x, -f x ∂sphereHaar _) at he
  rw [integral_neg] at he
  linarith

private theorem integral_coordinate_four_swap (i j : ι) :
    realSphereIntegral (fun x => realCoordinate x i ^ 4) =
      realSphereIntegral (fun x => realCoordinate x j ^ 4) := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := integral_sphereAction U (fun x => realCoordinate x i ^ 4)
  have hc : ∀ x : RealSphere ι, realCoordinate (sphereAction U x) i = realCoordinate x j := by
    intro x
    change x.val ((Equiv.swap i j).symm i) = _
    simp
  simpa only [hc] using h.symm

theorem integral_coordinate_four_eq_three_mixed (i j : ι) (hij : i ≠ j) :
    realSphereIntegral (fun x => realCoordinate x i ^ 4) =
      3 * realSphereIntegral (fun x => realCoordinate x i ^ 2 * realCoordinate x j ^ 2) := by
  let X (x : RealSphere ι) := realCoordinate x i
  let Y (x : RealSphere ι) := realCoordinate x j
  have hX : Continuous X := realCoordinate_continuous i
  have hY : Continuous Y := realCoordinate_continuous j
  have ho₁ : realSphereIntegral (fun x => X x ^ 3 * Y x) = 0 := by
    apply integral_odd_signFlip_zero i
    intro x
    change realCoordinate (sphereAction (signFlip i) x) i ^ 3 *
      realCoordinate (sphereAction (signFlip i) x) j = _
    simp only [signFlip_apply, ite_true, if_neg (Ne.symm hij), X, Y]
    ring
  have ho₂ : realSphereIntegral (fun x => X x * Y x ^ 3) = 0 := by
    apply integral_odd_signFlip_zero i
    intro x
    change realCoordinate (sphereAction (signFlip i) x) i *
      realCoordinate (sphereAction (signFlip i) x) j ^ 3 = _
    simp only [signFlip_apply, ite_true, if_neg (Ne.symm hij), X, Y]
    ring
  have h₄ : (Real.sqrt (1 / 2)) ^ 4 = (1 / 4 : ℝ) := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, reflectionFactor_sq]
    norm_num
  have h := integral_sphereAction (reflectPairIsometry i j hij)
    (fun x => realCoordinate x i ^ 4)
  simp only [reflectPairIsometry_apply_left, mul_pow, h₄] at h
  change realSphereIntegral (fun x => (1 / 4) * (X x + Y x) ^ 4) =
    realSphereIntegral (fun x => X x ^ 4) at h
  have hpoly (x : RealSphere ι) : (1 / 4) * (X x + Y x) ^ 4 =
      (1 / 4) * (X x ^ 4 + 4 * (X x ^ 3 * Y x) +
        6 * (X x ^ 2 * Y x ^ 2) + 4 * (X x * Y x ^ 3) + Y x ^ 4) := by ring
  simp_rw [hpoly, integral_const_mul] at h
  rw [integral_add, integral_add, integral_add, integral_add] at h <;>
    try solve | exact sphereHaar_integrable_continuous _ (by fun_prop)
  simp only [integral_const_mul] at h
  change (1 / 4) * (realSphereIntegral (fun x => X x ^ 4) +
    4 * realSphereIntegral (fun x => X x ^ 3 * Y x) +
    6 * realSphereIntegral (fun x => X x ^ 2 * Y x ^ 2) +
    4 * realSphereIntegral (fun x => X x * Y x ^ 3) +
    realSphereIntegral (fun x => Y x ^ 4)) = realSphereIntegral (fun x => X x ^ 4) at h
  rw [ho₁, ho₂, show realSphereIntegral (fun x => Y x ^ 4) =
    realSphereIntegral (fun x => X x ^ 4) from integral_coordinate_four_swap j i] at h
  change realSphereIntegral (fun x => X x ^ 4) = 3 * realSphereIntegral (fun x => X x ^ 2 * Y x ^ 2)
  linarith


private theorem integral_coordinate_two_swap (i j : ι) :
    realSphereIntegral (fun x => realCoordinate x i ^ 2) =
      realSphereIntegral (fun x => realCoordinate x j ^ 2) := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := integral_sphereAction U (fun x => realCoordinate x i ^ 2)
  have hc : ∀ x : RealSphere ι, realCoordinate (sphereAction U x) i = realCoordinate x j := by
    intro x
    change x.val ((Equiv.swap i j).symm i) = _
    simp
  simpa only [hc] using h.symm

theorem integral_coordinate_sq (i : ι) :
    realSphereIntegral (fun x => realCoordinate x i ^ 2) = 1 / (Fintype.card ι : ℝ) := by
  letI : Nonempty ι := ⟨i⟩
  have hD : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have h := realSphereIntegral_congr (fun x : RealSphere ι => realSphere_sum_sq x)
  change (∫ x : RealSphere ι, ∑ j, realCoordinate x j ^ 2 ∂sphereHaar _) = _ at h
  have hInt (j : ι) : Integrable (fun x : RealSphere ι => realCoordinate x j ^ 2)
      (sphereHaar (EuclideanSpace ℝ ι)) :=
    sphereHaar_integrable_continuous _ ((realCoordinate_continuous j).pow 2)
  rw [integral_finsetSum Finset.univ (fun j _ => hInt j)] at h
  have hRewrite (j : ι) : realSphereIntegral (fun x => realCoordinate x j ^ 2) =
      realSphereIntegral (fun x => realCoordinate x i ^ 2) :=
    integral_coordinate_two_swap j i
  simp_rw [hRewrite] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, integral_const, probReal_univ,
    one_smul] at h
  exact (eq_div_iff hD).mpr (by simpa only [mul_comm] using h)

theorem integral_coordinate_four (i : ι) :
    realSphereIntegral (fun x => realCoordinate x i ^ 4) =
      3 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 2)) := by
  letI : Nonempty ι := ⟨i⟩
  let D : ℝ := Fintype.card ι
  let A := realSphereIntegral (fun x => realCoordinate x i ^ 4)
  have hD : 0 < D := by positivity
  have hEq (x : RealSphere ι) :
      (∑ j, realCoordinate x i ^ 2 * realCoordinate x j ^ 2) = realCoordinate x i ^ 2 := by
    rw [← Finset.mul_sum, realSphere_sum_sq, mul_one]
  have h := realSphereIntegral_congr hEq
  change (∫ x : RealSphere ι, ∑ j, realCoordinate x i ^ 2 * realCoordinate x j ^ 2 ∂sphereHaar _) =
      realSphereIntegral _ at h
  have hInt (j : ι) : Integrable (fun x : RealSphere ι =>
      realCoordinate x i ^ 2 * realCoordinate x j ^ 2) (sphereHaar (EuclideanSpace ℝ ι)) :=
    sphereHaar_integrable_continuous _ (((realCoordinate_continuous i).pow 2).mul
      ((realCoordinate_continuous j).pow 2))
  rw [integral_finsetSum Finset.univ (fun j _ => hInt j), integral_coordinate_sq] at h
  have hErase (j : ι) (hj : j ∈ (Finset.univ : Finset ι).erase i) :
      realSphereIntegral (fun x => realCoordinate x i ^ 2 * realCoordinate x j ^ 2) = A / 3 := by
    have h := integral_coordinate_four_eq_three_mixed i j (Finset.ne_of_mem_erase hj).symm
    change A = _ at h
    linarith
  have hi : realSphereIntegral (fun x => realCoordinate x i ^ 2 * realCoordinate x i ^ 2) = A := by
    apply realSphereIntegral_congr
    intro x
    ring
  change (∑ j, realSphereIntegral (fun x => realCoordinate x i ^ 2 * realCoordinate x j ^ 2)) =
    1 / D at h
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hi,
    Finset.sum_congr rfl hErase, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at h
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = D - 1 :=
    by simpa only [D, Nat.cast_one] using (Nat.cast_sub (R := ℝ) (show 1 ≤ Fintype.card ι from Fintype.card_pos))
  rw [hcast] at h
  have he : A * (D + 2) = 3 * (1 / D) := by nlinarith
  change A = _
  apply (eq_div_iff (by positivity)).mpr
  calc
    A * (D * (D + 2)) = (A * (D + 2)) * D := by ring
    _ = 3 := by rw [he]; field_simp

theorem integral_coordinate_pair_sq (i j : ι) (hij : i ≠ j) :
    realSphereIntegral (fun x => realCoordinate x i ^ 2 * realCoordinate x j ^ 2) =
      1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 2)) := by
  have h := integral_coordinate_four_eq_three_mixed i j hij
  rw [integral_coordinate_four] at h
  rw [← mul_one_div] at h
  exact (mul_left_cancel₀ (show (3 : ℝ) ≠ 0 by norm_num) h.symm)

private theorem integral_coordinate_four_of_singleton (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) :
    realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
        realCoordinate x k * realCoordinate x l) = 0 := by
  apply integral_odd_signFlip_zero i
  intro x
  simp only [signFlip_apply, ite_true, if_neg (Ne.symm hij), if_neg (Ne.symm hik), if_neg (Ne.symm hil)]
  ring

/-- Four real coordinate factors contract to the three pairings. -/
theorem integral_four_real_coordinate (i j k l : ι) :
    realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
        realCoordinate x k * realCoordinate x l) =
      ((if i = j ∧ k = l then (1 : ℝ) else 0) +
        (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) /
      ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 2)) := by
  have hnone (i j k l : ι) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) :
      realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
          realCoordinate x k * realCoordinate x l) = 0 :=
    integral_coordinate_four_of_singleton i j k l hij hik hil
  have hperm (i j k l : ι) :
      realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
          realCoordinate x k * realCoordinate x l) =
        realSphereIntegral (fun x => realCoordinate x j * realCoordinate x i *
          realCoordinate x k * realCoordinate x l) := realSphereIntegral_congr (by intro x; ring)
  have hperm' (i j k l : ι) :
      realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
          realCoordinate x k * realCoordinate x l) =
        realSphereIntegral (fun x => realCoordinate x k * realCoordinate x i *
          realCoordinate x j * realCoordinate x l) := realSphereIntegral_congr (by intro x; ring)
  have hperm'' (i j k l : ι) :
      realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
          realCoordinate x k * realCoordinate x l) =
        realSphereIntegral (fun x => realCoordinate x l * realCoordinate x i *
          realCoordinate x j * realCoordinate x k) := realSphereIntegral_congr (by intro x; ring)
  have hfour (i : ι) :
      realSphereIntegral (fun x => realCoordinate x i * realCoordinate x i *
          realCoordinate x i * realCoordinate x i) =
        3 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 2)) :=
    (realSphereIntegral_congr (by intro x; ring)).trans (integral_coordinate_four i)
  have hpair (i j : ι) (hij : i ≠ j) :
      realSphereIntegral (fun x => realCoordinate x i * realCoordinate x i *
          realCoordinate x j * realCoordinate x j) =
        1 / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 2)) :=
    (realSphereIntegral_congr (by intro x; ring)).trans (integral_coordinate_pair_sq i j hij)
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      by_cases hil : i = l
      · subst l
        norm_num at ⊢
        exact hfour i
      · rw [hperm'' i i i l, hnone l i i i (Ne.symm hil) (Ne.symm hil) (Ne.symm hil)]
        simp [hil]
    · by_cases hkl : k = l
      · subst l
        simpa [hik] using hpair i k hik
      · rw [hperm' i i k l, hnone k i i l (Ne.symm hik) (Ne.symm hik) hkl]
        simp [hik, hkl]
  · by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        rw [show realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
            realCoordinate x i * realCoordinate x j) =
              realSphereIntegral (fun x => realCoordinate x i * realCoordinate x i *
                realCoordinate x j * realCoordinate x j) from realSphereIntegral_congr (by intro x; ring)]
        simpa [hij] using hpair i j hij
      · rw [hperm i j i l, hnone j i i l (Ne.symm hij) (Ne.symm hij) hjl]
        simp [hij, hjl, Ne.symm hij]
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          rw [show realSphereIntegral (fun x => realCoordinate x i * realCoordinate x j *
              realCoordinate x j * realCoordinate x i) =
                realSphereIntegral (fun x => realCoordinate x i * realCoordinate x i *
                  realCoordinate x j * realCoordinate x j) from realSphereIntegral_congr (by intro x; ring)]
          simpa [hij] using hpair i j hij
        · rw [hperm i j k i, hnone j i k i (Ne.symm hij) hjk (Ne.symm hij)]
          simp [hij, hik, hjk]
      · rw [hnone i j k l hij hik hil]
        simp [hij, hik, hil]

#print axioms integral_coordinate_sq
#print axioms integral_coordinate_four
#print axioms integral_four_real_coordinate

#print axioms integral_coordinate_four_eq_three_mixed

end
end CriticalDepth.FaultAverageInfidelity
