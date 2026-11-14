import CSSRandomDistanceCounts
import CSSRandomJointSample
import CSSRandomLinearBound

/-!
Existence of the two CSS check spaces under the simultaneous sparse exclusions.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

noncomputable section

def cssRigidityXBad (R : ℕ) (p : BW (cssSites R)) (G : XCheckSample p (cssXDimension R)) : Prop :=
  badXCheckSample p (cssDistance R) (R * (cssXDimension R + 1)) G ∨ badSparseLinearSample p R G

def cssRigidityZBad (R : ℕ) (H : Submodule CSSBit (BW (cssSites R)))
    (D : Fin (cssZDimension R) → cssOrthogonal H) : Prop :=
  (∀ x ∈ H, x ≠ 0 → R * (cssXDimension R + 1) < wordWeight x) ∧
    badZCheckSample H (cssDeletionThreshold R) (R * (cssXDimension R + 1)) D

def cssRigidityQBad (R : ℕ) (p : BW (cssSites R))
    (z : CSSJointSample p (cssXDimension R) (cssZDimension R)) : Prop :=
  ∃ Q : Matrix (Fin (cssSites R)) (Fin (cssSites R)) CSSBit, Q ≠ 0 ∧ Q.IsSymm ∧
    (∀ i, wordWeight (Q.row i) ≤ R + 1) ∧
    jointSymmetricBad p (cssXDimension R) (cssZDimension R) Q z

/-- The three bad-event counts in the uniform generator sample,
with rank-deficient samples included in the first event. -/
def cssRigidityBadCount (R : ℕ) (p : BW (cssSites R)) : ℕ :=
  Nat.card {z : CSSJointSample p (cssXDimension R) (cssZDimension R) // cssRigidityXBad R p z.1} +
    Nat.card {z : CSSJointSample p (cssXDimension R) (cssZDimension R) //
      jointConditionalEvent p (cssXDimension R) (cssZDimension R) (cssRigidityZBad R) z} +
    Nat.card {z : CSSJointSample p (cssXDimension R) (cssZDimension R) // cssRigidityQBad R p z}

theorem cssRigidityBadCount_scaled (R : ℕ) (hR : 2 ^ 20 ≤ R)
    (p : BW (cssSites R)) (hp : wordWeight p = cssDistance R) :
    cssRigidityBadCount R p * 2 ^ (R - 2) ≤
      Nat.card (CSSJointSample p (cssXDimension R) (cssZDimension R)) := by
  classical
  let n := cssSites R
  let a := cssXDimension R
  let b := cssZDimension R
  let d := cssDistance R
  let W := R * (a + 1)
  have hRp : 0 < R := by omega
  have hdim := css_logicalDimension_positive R (by omega)
  have hdist : d ≤ n := Nat.pow_le_pow_right hRp (by decide)
  have hp₀ : p ≠ 0 := by
    rintro rfl
    have hpos : 0 < d := by dsimp [d, cssDistance]; positivity
    simp [wordWeight] at hp
    omega
  let X := XCheckSample p a
  let Z := CSSJointSample p a b
  let xBad := cssRigidityXBad R p
  let zBad := cssRigidityZBad R
  let qBad := cssRigidityQBad R p
  have hxD := css_planted_card_distance_bad R hR p hp₀
  have hxL : Nat.card {G : X // badSparseLinearSample p R G} * 2 ^ R ≤ Nat.card X := by
    have hN : R + 1 ≤ n := by
      have hR2 : R + 1 ≤ R ^ 2 := by nlinarith
      exact hR2.trans hdist
    have hB := css_sparse_linear_coefficient_budget R hR
    exact card_badSparseLinearSample_scaled p hp₀ R (R ^ 2 / 16)
      (by dsimp [n, cssSites]; positivity) hB.1
      ((css_bound_for_matrix_shells R R hR hN).trans (Nat.pow_le_pow_right (by decide) hB.2))
      (R / 256) R (twelve_pow_bound R hR) (css_linear_global_slack R hR)
  have hx : Nat.card {G : X // xBad G} * 2 ^ (R - 1) ≤ Nat.card X := by
    have hunion : Nat.card {G : X // xBad G} ≤
        Nat.card {G : X // badXCheckSample p d W G} +
          Nat.card {G : X // badSparseLinearSample p R G} := by
      letI : Fintype X := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]
      have he : (Finset.univ.filter xBad) =
          (Finset.univ.filter fun G : X => badXCheckSample p d W G) ∪
            (Finset.univ.filter fun G : X => badSparseLinearSample p R G) := by
        ext G
        simp [xBad, cssRigidityXBad, d, W, a]
      rw [he]
      exact Finset.card_union_le _ _
    have htwice : (2 : ℕ) ^ R = 2 * 2 ^ (R - 1) := by
      rw [← pow_succ', show R - 1 + 1 = R by omega]
    have hxD' : 2 * (Nat.card {G : X // badXCheckSample p d W G} * 2 ^ (R - 1)) ≤
        Nat.card X := by
      simpa only [htwice, mul_left_comm] using hxD
    have hxL' : 2 * (Nat.card {G : X // badSparseLinearSample p R G} * 2 ^ (R - 1)) ≤
        Nat.card X := by
      simpa only [htwice, mul_left_comm] using hxL
    exact (Nat.mul_le_mul_right _ hunion).trans (by rw [Nat.add_mul]; omega)
  have hxc := card_joint_x_bad_le p a b xBad (2 ^ (R - 1)) hx
  have hzc : Nat.card {z : Z // jointConditionalEvent p a b zBad z} * 2 ^ R ≤ Nat.card Z := by
    have h := card_joint_conditional_le p a b zBad (2 ^ R) 1 (by
      intro G H hr
      by_cases hH : ∀ x ∈ H, x ≠ 0 → W < wordWeight x
      · let P := fun D : Fin b → cssOrthogonal H => badZCheckSample H (cssDeletionThreshold R) W D
        have he : Nat.card {D : Fin b → cssOrthogonal H // zBad H D} =
            Nat.card {D : Fin b → cssOrthogonal H // P D} := by
          apply Nat.card_congr (Equiv.subtypeEquivRight _)
          intro D
          exact ⟨And.right, fun hd => ⟨hH, hd⟩⟩
        rw [he, one_mul, ← zSample_card_eq_coefficients H hr b]
        exact css_z_card_distance_bad R hR H hr hH
      · letI : IsEmpty {D : Fin b → cssOrthogonal H // zBad H D} :=
          ⟨fun D => hH D.property.1⟩
        simp)
    simpa only [one_mul] using h
  letI : Fintype Z := Fintype.ofFinite _
  have hcodim := (css_z_check_scale R hR).2.2
  have hrp : R + 1 < wordWeight p := by
    rw [hp]
    exact cssDistance_gt_localBound R (by omega)
  have hn : 0 < n := by dsimp [n, cssSites]; positivity
  have hw : R + 2 ≤ n := by
    have hR2 : R + 2 ≤ R ^ 2 := by nlinarith
    exact hR2.trans hdist
  have hq0 := card_symmetric_bad_union_le (jointSymmetricBad p a b) hn (R + 1) a
    ((R / 256) * (R + 3)) (R / 256 + R + 1) 2
    (css_bound_for_matrix_shells R (R + 1) hR hw)
    (fun u hu _ => css_symmetric_row_slack R u hR hu)
    (fun Q hQ hs hRow => by
      rw [← Nat.card_eq_fintype_card]
      exact card_jointSymmetricBad_rows_le p a b (R + 1)
        (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hdim)) hcodim (by omega)
        hrp Q hQ hs hRow)
  have hqc : Nat.card {z : Z // qBad z} * 2 ^ R ≤ Nat.card Z := by
    have hpow : (2 : ℕ) ^ (R / 256 + R + 1) = 2 ^ R * (2 * 2 ^ (R / 256)) := by
      rw [pow_succ, pow_add]
      ring
    rw [hpow, ← Nat.mul_assoc, ← Nat.card_eq_fintype_card] at hq0
    have h := hq0.trans (Nat.mul_le_mul_right _ (twelve_pow_bound R hR))
    apply Nat.le_of_mul_le_mul_right _ (show 0 < 2 * (2 : ℕ) ^ (R / 256) from by positivity)
    exact h.trans_eq (by ring)
  have h₁ : (2 : ℕ) ^ (R - 1) = 2 * 2 ^ (R - 2) := by
    rw [← pow_succ', show R - 2 + 1 = R - 1 by omega]
  have h₂ : (2 : ℕ) ^ R = 4 * 2 ^ (R - 2) := by
    calc
      _ = (2 : ℕ) ^ ((R - 1) + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ', h₁]; ring
  have hxc' : 2 * (Nat.card {z : Z // xBad z.1} * 2 ^ (R - 2)) ≤ Nat.card Z := by
    simpa only [h₁, mul_left_comm] using hxc
  have hzc' : 4 * (Nat.card {z : Z // jointConditionalEvent p a b zBad z} * 2 ^ (R - 2)) ≤
      Nat.card Z := by
    simpa only [h₂, mul_left_comm] using hzc
  have hqc' : 4 * (Nat.card {z : Z // qBad z} * 2 ^ (R - 2)) ≤ Nat.card Z := by
    simpa only [h₂, mul_left_comm] using hqc
  change (Nat.card {z : Z // xBad z.1} +
    Nat.card {z : Z // jointConditionalEvent p a b zBad z} +
    Nat.card {z : Z // qBad z}) * 2 ^ (R - 2) ≤ Nat.card Z
  rw [Nat.add_mul, Nat.add_mul]
  omega

/-- Every designated word of the required weight can be used in the planted sample. -/
theorem exists_rigid_checkSpaces_for_planted (R : ℕ) (hR : 2 ^ 20 ≤ R)
    (p : CSSWord (cssSites R)) (hp : wordWeight p = cssDistance R) :
    ∃ H J : Submodule CSSBit (CSSWord (cssSites R)),
      RigidityCheckSpaces H J R ∧ Module.finrank CSSBit H = cssXDimension R ∧
      Module.finrank CSSBit J = cssZDimension R ∧ p ∈ cssOrthogonal H ∧
      ∀ x ∈ cssOrthogonal H, x ≠ 0 → cssDistance R ≤ wordWeight x := by
  let n := cssSites R
  let a := cssXDimension R
  let b := cssZDimension R
  let W := R * (a + 1)
  have hRp : 0 < R := by omega
  have hdim := css_logicalDimension_positive R (by omega)
  let X := XCheckSample p a
  let Z := CSSJointSample p a b
  let xBad := cssRigidityXBad R p
  let zBad := cssRigidityZBad R
  let qBad := cssRigidityQBad R p
  have hfull (G : X) (hG : ¬ xBad G) :
      Module.finrank CSSBit (columnsToWord G).range = a :=
    (good_xChecks_of_not_bad p hp G (fun h => hG (Or.inl h))).2.1
  letI : Fintype Z := Fintype.ofFinite _
  have hPos : 0 < Nat.card Z := by
    letI : Nonempty Z := ⟨(0, 0)⟩
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hsmall : cssRigidityBadCount R p < Nat.card Z := by
    have hscaled : cssRigidityBadCount R p * 2 ^ (R - 2) ≤ Nat.card Z :=
      cssRigidityBadCount_scaled R hR p hp
    have hpow : 2 ≤ (2 : ℕ) ^ (R - 2) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (show 1 ≤ R - 2 by omega)
    have hh := (Nat.mul_le_mul_left (cssRigidityBadCount R p) hpow).trans hscaled
    omega
  obtain ⟨G, D, hH, hX, hZ, hQ⟩ := exists_good_CSSJointSample p a b xBad zBad qBad hfull hsmall
  let H := (columnsToWord G).range
  let J := (zColumnsToWord H (zSampleEquiv H hH b D)).range
  obtain ⟨hinj, _, hPH, hA, hDual⟩ :=
    good_xChecks_of_not_bad p hp G (fun h => hX (Or.inl h))
  let T := cssDeletionThreshold R
  obtain ⟨hJ, hJH, hPrimal, hDualJ⟩ :=
    good_zChecks_of_not_bad H T W (zSampleEquiv H hH b D) (fun h => hZ ⟨hA, h⟩)
  have hCompat : H ≤ cssOrthogonal J := cssChecksCompatible_symm.mpr hJH
  refine ⟨H, J, ?_, hH, hJ, hPH, hDual⟩
  refine ⟨hCompat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hH]
    change 1 ≤ R ^ 4
    exact pow_pos hRp _
  · rw [hH, hJ]
    exact hdim
  · intro v hv hn
    exact (cssDistance_gt_localBound R (by omega)).trans_le (hDual v hv hn)
  · intro v hv hn
    rw [hH]
    exact hDualJ v hv hn
  · intro v hv hn
    rw [hH, hJ]
    exact hPrimal v hv hn
  · intro F hF
    obtain ⟨S, hS⟩ := exists_intertwiner_of_range_preservation F (columnsToWord G) hinj hF.2.2.2.le
    by_contra hF₀
    by_cases hS₀ : S = 1
    · subst S
      exact hF₀ (sparse_linear_eq_one_of_trivial_intertwiner F (columnsToWord G) R hF.2.1
        (fun v hv h₀ => (cssDistance_gt_localBound R (by omega)).trans_le (hDual v hv h₀)) hS)
    · exact hX (Or.inr ⟨F, S, hF₀, hS₀, hF.1.2, hF.2.1, hF.2.2.1, hS⟩)
  · intro Q hs hw hMap
    by_contra hnq
    apply hQ
    refine ⟨Q, hnq, hs, hw, hH, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hMap v hv

theorem exists_rigid_checkSpaces (R : ℕ) (hR : 2 ^ 20 ≤ R) :
    ∃ (H J : Submodule CSSBit (CSSWord (cssSites R))) (p : CSSWord (cssSites R)),
      RigidityCheckSpaces H J R ∧ Module.finrank CSSBit H = cssXDimension R ∧
      Module.finrank CSSBit J = cssZDimension R ∧ p ∈ cssOrthogonal H ∧
      wordWeight p = cssDistance R ∧
      ∀ x ∈ cssOrthogonal H, x ≠ 0 → cssDistance R ≤ wordWeight x := by
  have hRpos : 0 < R := by omega
  have hdist : cssDistance R ≤ cssSites R := Nat.pow_le_pow_right hRpos (by decide)
  obtain ⟨p, hp⟩ := plantWordOfWeight_exists (cssSites R) (cssDistance R) hdist
  obtain ⟨H, J, hRigid, hH, hJ, hPlanted, hDual⟩ :=
    exists_rigid_checkSpaces_for_planted R hR p hp
  exact ⟨H, J, p, hRigid, hH, hJ, hPlanted, hp, hDual⟩

#print axioms cssRigidityBadCount_scaled
#print axioms exists_rigid_checkSpaces_for_planted
#print axioms exists_rigid_checkSpaces

end

end CriticalDepth.Manuscript20261114.CSSCheckSpaces