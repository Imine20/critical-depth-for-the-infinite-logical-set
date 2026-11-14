import FaultHaarRealMoments

/-!
The normalized spherical Haar probability yields the complex coordinate
fourth moment used in the average logical gate infidelity formula.
-/

namespace CriticalDepth.FaultAverageInfidelity

noncomputable section

open MeasureTheory Matrix Metric
open CriticalDepth.FaultEntanglementFidelity
open scoped BigOperators

variable {Log : Type*} [Fintype Log] [DecidableEq Log] [Nonempty Log]

abbrev LogicalSphere (Log : Type*) [Fintype Log] := RealSphere (Log × Bool)

def logicalSphereVector (x : LogicalSphere Log) (i : Log) : ℂ :=
  (realCoordinate x (i, false) : ℂ) + Complex.I * (realCoordinate x (i, true) : ℂ)

theorem logicalSphereVector_unit (x : LogicalSphere Log) :
    ∑ i, Complex.normSq (logicalSphereVector x i) = 1 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Log × Bool => ℝ) x.val
  rw [mem_sphere_zero_iff_norm.mp x.property] at h
  simp only [Real.norm_eq_abs, sq_abs, one_pow, Fintype.sum_prod_type, Fintype.sum_bool] at h
  calc
    _ = ∑ i, (realCoordinate x (i, true) ^ 2 + realCoordinate x (i, false) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [logicalSphereVector, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
        Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    _ = 1 := h.symm

private theorem logicalSphereVector_continuous (i : Log) :
    Continuous (fun x : LogicalSphere Log => logicalSphereVector x i) := by
  have hc (b : Bool) : Continuous (fun x : LogicalSphere Log => realCoordinate x (i, b)) :=
    (PiLp.continuous_apply 2 (fun _ : Log × Bool => ℝ) (i, b)).comp continuous_subtype_val
  exact (Complex.continuous_ofReal.comp (hc false)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (hc true)))

private def phaseCoeff (negative bit : Bool) : ℂ :=
  if bit then if negative then -Complex.I else Complex.I else 1

private theorem logicalSphereVector_phase (x : LogicalSphere Log) (i : Log) (c : Bool) :
    (if c then star (logicalSphereVector x i) else logicalSphereVector x i) =
      ∑ b : Bool, phaseCoeff c b * (realCoordinate x (i, b) : ℂ) := by
  cases c <;>
    simp [Fintype.sum_bool, logicalSphereVector, phaseCoeff, add_comm]

private theorem phaseCoeff_pair_sum (c d : Bool) :
    (∑ b : Bool, phaseCoeff c b * phaseCoeff d b) = if c = d then 0 else 2 := by
  cases c <;> cases d <;> norm_num [Fintype.sum_bool, phaseCoeff, Complex.I_mul_I]

private theorem phaseCoeff_indicator_sum (i j : Log) (c d : Bool) :
    (∑ a : Bool, ∑ b : Bool,
      phaseCoeff c a * phaseCoeff d b * (if (i, a) = (j, b) then 1 else 0)) =
      if i = j then (if c = d then 0 else 2) else 0 := by
  by_cases h : i = j
  · subst j
    have hs (a : Bool) :
        (∑ b : Bool, phaseCoeff c a * phaseCoeff d b * (if (i, a) = (i, b) then 1 else 0)) =
          phaseCoeff c a * phaseCoeff d a := by simp
    simp_rw [hs, phaseCoeff_pair_sum]
    simp
  · simp [h]

private theorem coefficient_sum_pairing
    (i j k l : Log) (c d e f : Bool) :
    (∑ a : Bool, ∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
      (phaseCoeff c a * phaseCoeff d b * phaseCoeff e u * phaseCoeff f v) *
        (if (i, a) = (j, b) ∧ (k, u) = (l, v) then 1 else 0)) =
      (if i = j then (if c = d then 0 else 2) else 0) *
        (if k = l then (if e = f then 0 else 2) else 0) := by
  let P (a b : Bool) := phaseCoeff c a * phaseCoeff d b *
    (if (i, a) = (j, b) then 1 else 0)
  let Q (u v : Bool) := phaseCoeff e u * phaseCoeff f v *
    (if (k, u) = (l, v) then 1 else 0)
  calc
    _ = ∑ a, ∑ b, P a b * (∑ u, ∑ v, Q u v) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h₁ : (i, a) = (j, b) <;> by_cases h₂ : (k, u) = (l, v) <;>
        simp only [P, Q, h₁, h₂, true_and, false_and, and_false, ite_true, ite_false,
          one_mul, mul_one, zero_mul, mul_zero] <;> ring
    _ = _ := by
      simp only [← Finset.sum_mul]
      exact congrArg₂ (· * ·) (phaseCoeff_indicator_sum i j c d) (phaseCoeff_indicator_sum k l e f)

private theorem logicalVector_expansion (p q : Log × Log) (x : LogicalSphere Log) :
    fourthTerm logicalSphereVector p q x =
      ∑ a : Bool, ∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
        (phaseCoeff false a * phaseCoeff true b * phaseCoeff true u * phaseCoeff false v) *
          ((realCoordinate x (p.1, a) * realCoordinate x (p.2, b) *
            realCoordinate x (q.1, u) * realCoordinate x (q.2, v) : ℝ) : ℂ) := by
  unfold fourthTerm
  have h₁ := logicalSphereVector_phase x p.1 false
  have h₂ := logicalSphereVector_phase x p.2 true
  have h₃ := logicalSphereVector_phase x q.1 true
  have h₄ := logicalSphereVector_phase x q.2 false
  change logicalSphereVector x p.1 = _ at h₁
  change star (logicalSphereVector x p.2) = _ at h₂
  change star (logicalSphereVector x q.1) = _ at h₃
  change logicalSphereVector x q.2 = _ at h₄
  let A (a : Bool) : ℂ := phaseCoeff false a * (realCoordinate x (p.1, a) : ℂ)
  let B (b : Bool) : ℂ := phaseCoeff true b * (realCoordinate x (p.2, b) : ℂ)
  let C (u : Bool) : ℂ := phaseCoeff true u * (realCoordinate x (q.1, u) : ℂ)
  let E (v : Bool) : ℂ := phaseCoeff false v * (realCoordinate x (q.2, v) : ℂ)
  have hprod (F G : Bool → ℂ) : (∑ i, F i) * (∑ j, G j) = ∑ i, ∑ j, F i * G j := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [h₁, h₂, h₃, h₄]
  change ((∑ a, A a) * (∑ b, B b)) * ((∑ u, C u) * (∑ v, E v)) = _
  rw [hprod A B, hprod C E, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  dsimp [A, B, C, E]
  push_cast
  ring

theorem fourthTerm_sphereHaar_integrable (p q : Log × Log) :
    Integrable (fourthTerm logicalSphereVector p q)
      (sphereHaar (EuclideanSpace ℝ (Log × Bool))) := by
  apply sphereHaar_integrable_continuous
  have h₁ := logicalSphereVector_continuous p.1
  have h₂ := logicalSphereVector_continuous p.2
  have h₃ := logicalSphereVector_continuous q.1
  have h₄ := logicalSphereVector_continuous q.2
  unfold fourthTerm
  fun_prop

theorem sphereHaar_fourthMoment (p q : Log × Log) :
    (∫ x, fourthTerm logicalSphereVector p q x
      ∂sphereHaar (EuclideanSpace ℝ (Log × Bool))) = fourthMoment p q := by
  classical
  let D : ℂ := (Fintype.card Log : ℂ) * ((Fintype.card Log : ℂ) + 1)
  let mulCoeff (a b u v : Bool) :=
    phaseCoeff false a * phaseCoeff true b * phaseCoeff true u * phaseCoeff false v
  let r (a b u v : Bool) (x : LogicalSphere Log) :=
    realCoordinate x (p.1, a) * realCoordinate x (p.2, b) *
      realCoordinate x (q.1, u) * realCoordinate x (q.2, v)
  let P (a b u v : Bool) : Prop := (p.1, a) = (p.2, b) ∧ (q.1, u) = (q.2, v)
  let Q (a b u v : Bool) : Prop := (p.1, a) = (q.1, u) ∧ (p.2, b) = (q.2, v)
  let R (a b u v : Bool) : Prop := (p.1, a) = (q.2, v) ∧ (p.2, b) = (q.1, u)
  let I (P : Prop) [Decidable P] : ℂ := if P then 1 else 0
  have hI (a b u v : Bool) :
      Integrable (fun x => mulCoeff a b u v * (r a b u v x : ℂ))
        (sphereHaar (EuclideanSpace ℝ (Log × Bool))) := by
    apply sphereHaar_integrable_continuous
    have hc (i : Log × Bool) :
        Continuous (fun x : LogicalSphere Log => realCoordinate x i) :=
      (PiLp.continuous_apply 2 (fun _ : Log × Bool => ℝ) i).comp continuous_subtype_val
    unfold mulCoeff r
    fun_prop
  have hR (a b u v : Bool) :
      (∫ x : LogicalSphere Log, (r a b u v x : ℂ)
        ∂sphereHaar (EuclideanSpace ℝ (Log × Bool))) =
        (I (P a b u v) + I (Q a b u v) + I (R a b u v)) / (4 * D) := by
    rw [integral_complex_ofReal]
    have h := integral_four_real_coordinate (p.1, a) (p.2, b) (q.1, u) (q.2, v)
    change (∫ x : LogicalSphere Log, r a b u v x ∂sphereHaar _) = _ at h
    rw [h]
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_ofNat]
    have hden : (Fintype.card Log : ℂ) * 2 * ((Fintype.card Log : ℂ) * 2 + 2) = 4 * D := by
      dsimp [D]
      ring
    rw [hden]
    congr 1
    have castI (S : Prop) [Decidable S] :
        ((if S then (1 : ℝ) else 0 : ℝ) : ℂ) = I S := by
      by_cases hS : S
      · simp only [I, if_pos hS, Complex.ofReal_one]
      · simp only [I, if_neg hS, Complex.ofReal_zero]
    simp only [P, Q, R, castI]
  have hP : (∑ a : Bool, ∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
      mulCoeff a b u v * I (P a b u v)) =
      if p.1 = p.2 ∧ q.1 = q.2 then 4 else 0 := by
    unfold mulCoeff I P
    rw [coefficient_sum_pairing]
    by_cases hi : p.1 = p.2 <;> by_cases hj : q.1 = q.2 <;> norm_num [hi, hj]
  have hQ : (∑ a : Bool, ∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
      mulCoeff a b u v * I (Q a b u v)) = if p = q then 4 else 0 := by
    simp only [Q, I, mulCoeff]
    have h (a : Bool) : (∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
        (phaseCoeff false a * phaseCoeff true b * phaseCoeff true u * phaseCoeff false v) *
          (if (p.1, a) = (q.1, u) ∧ (p.2, b) = (q.2, v) then 1 else 0)) =
        ∑ u : Bool, ∑ b : Bool, ∑ v : Bool,
          (phaseCoeff false a * phaseCoeff true u * phaseCoeff true b * phaseCoeff false v) *
            (if (p.1, a) = (q.1, u) ∧ (p.2, b) = (q.2, v) then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro v _
      ring
    simp_rw [h]
    rw [coefficient_sum_pairing]
    simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, Prod.ext_iff]
    by_cases hi : p.1 = q.1 <;> by_cases hj : p.2 = q.2 <;> norm_num [hi, hj]
  have hZ : (∑ a : Bool, ∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
      mulCoeff a b u v * I (R a b u v)) = 0 := by
    simp only [R, I, mulCoeff]
    have h (a : Bool) : (∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
        (phaseCoeff false a * phaseCoeff true b * phaseCoeff true u * phaseCoeff false v) *
          (if (p.1, a) = (q.2, v) ∧ (p.2, b) = (q.1, u) then 1 else 0)) =
        ∑ v : Bool, ∑ b : Bool, ∑ u : Bool,
          (phaseCoeff false a * phaseCoeff false v * phaseCoeff true b * phaseCoeff true u) *
            (if (p.1, a) = (q.2, v) ∧ (p.2, b) = (q.1, u) then 1 else 0) := by
      have he (b : Bool) : (∑ u : Bool, ∑ v : Bool,
          (phaseCoeff false a * phaseCoeff true b * phaseCoeff true u * phaseCoeff false v) *
            (if (p.1, a) = (q.2, v) ∧ (p.2, b) = (q.1, u) then 1 else 0)) =
          ∑ v : Bool, ∑ u : Bool,
            (phaseCoeff false a * phaseCoeff true b * phaseCoeff true u * phaseCoeff false v) *
              (if (p.1, a) = (q.2, v) ∧ (p.2, b) = (q.1, u) then 1 else 0) :=
        Finset.sum_comm
      simp_rw [he]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro u _
      ring
    simp_rw [h]
    rw [coefficient_sum_pairing]
    simp
  simp_rw [logicalVector_expansion]
  change (∫ x : LogicalSphere Log, ∑ a : Bool, ∑ b : Bool, ∑ u : Bool, ∑ v : Bool,
    mulCoeff a b u v * (r a b u v x : ℂ) ∂sphereHaar _) = _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => hI a b u v))))]
  simp_rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun u _ =>
    integrable_finsetSum _ (fun v _ => hI _ b u v))),
    integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => hI _ _ u v)),
    integral_finsetSum _ (fun v _ => hI _ _ _ v), integral_const_mul, hR,
    ← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib, hP, hQ, hZ, add_zero]
  unfold fourthMoment
  change ((if p.1 = p.2 ∧ q.1 = q.2 then (4 : ℂ) else 0) +
    (if p = q then 4 else 0)) / (4 * D) = _
  have hD : D ≠ 0 := by
    dsimp [D]
    have h₁ : (Fintype.card Log : ℝ) ≠ 0 := by positivity
    have h₂ : (Fintype.card Log : ℝ) + 1 ≠ 0 := by positivity
    exact mul_ne_zero (by exact_mod_cast h₁) (by exact_mod_cast h₂)
  change _ = ((if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0) +
    (if p = q then 1 else 0)) / D
  split_ifs <;> field_simp [hD] <;> ring

theorem averageInfidelity_sphereHaar_eq_dim_ratio_loss {Rec : Type*} [Fintype Rec]
    (K : Rec → Matrix Log Log ℂ) (hTP : ∑ k, (K k).conjTranspose * K k = 1) :
    averageInfidelity (sphereHaar (EuclideanSpace ℝ (Log × Bool))) logicalSphereVector K =
      ((Fintype.card Log : ℝ) / ((Fintype.card Log : ℝ) + 1)) * loss K :=
  averageInfidelity_eq_dim_ratio_loss _ _ fourthTerm_sphereHaar_integrable sphereHaar_fourthMoment K hTP

#print axioms logicalSphereVector_unit
#print axioms sphereHaar_fourthMoment
#print axioms averageInfidelity_sphereHaar_eq_dim_ratio_loss

end
end CriticalDepth.FaultAverageInfidelity
