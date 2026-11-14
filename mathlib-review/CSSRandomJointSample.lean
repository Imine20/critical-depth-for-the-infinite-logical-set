import CSSSparseSymmetricUnion
import CSSCodeDimension

/-!
A uniform joint sample represented by independent X-column choices and
a fixed-size tuple of binary coefficients. On the full-rank X event a
basis of the orthogonal space converts those coefficients bijectively to
the Z-column sample.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

noncomputable section
variable {n a b : ℕ}

abbrev XCheckSample (p : BW n) (a : ℕ) := Fin a → PlantedColumnSpace p

abbrev ZCheckCoefficients (n a b : ℕ) := Fin b → Fin (n - a) → CSSBit

abbrev CSSJointSample (p : BW n) (a b : ℕ) := XCheckSample p a × ZCheckCoefficients n a b

def zSampleEquiv (H : Submodule CSSBit (BW n))
    (hH : Module.finrank CSSBit H = a) (b : ℕ) :
    ZCheckCoefficients n a b ≃ (Fin b → cssOrthogonal H) :=
  let hd := (cssOrthogonal_finrank H).trans (congrArg (fun d => n - d) hH)
  let basis := Module.finBasisOfFinrankEq CSSBit (cssOrthogonal H) hd
  Equiv.piCongrRight fun _ => basis.equivFun.symm.toEquiv

theorem card_zCoefficients_predicate_eq
    (H : Submodule CSSBit (BW n)) (hH : Module.finrank CSSBit H = a) (b : ℕ)
    (P : (Fin b → cssOrthogonal H) → Prop) :
    Nat.card {z : ZCheckCoefficients n a b // P (zSampleEquiv H hH b z)} =
      Nat.card {G : Fin b → cssOrthogonal H // P G} :=
  Nat.card_congr ((zSampleEquiv H hH b).subtypeEquiv (fun _ => Iff.rfl))

private theorem card_prod_leftPredicate {X Y : Type*} (P : X → Prop) :
    Nat.card {z : X × Y // P z.1} = Nat.card {x : X // P x} * Nat.card Y := by
  let e : {z : X × Y // P z.1} ≃ ({x : X // P x} × Y) :=
    { toFun := fun z => (⟨z.val.1, z.property⟩, z.val.2)
      invFun := fun z => ⟨(z.1.val, z.2), z.1.property⟩
      left_inv := by rintro ⟨⟨x, y⟩, hx⟩; rfl
      right_inv := by rintro ⟨⟨x, hx⟩, y⟩; rfl }
  rw [Nat.card_congr e, Nat.card_prod]

private theorem card_predicate_or_le {V : Type*} [Finite V] (P Q : V → Prop) :
    Nat.card {x : V // P x ∨ Q x} ≤ Nat.card {x : V // P x} + Nat.card {x : V // Q x} := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]
  have he : (Finset.univ.filter fun x : V => P x ∨ Q x) =
      (Finset.univ.filter P) ∪ (Finset.univ.filter Q) := by
    ext x
    simp
  rw [he]
  exact Finset.card_union_le _ _

private theorem card_prod_predicate_bound {X Y : Type*} [Finite X] [Finite Y]
    (P : X → Y → Prop) (m M : ℕ)
    (h : ∀ x, Nat.card {y : Y // P x y} * m ≤ M) :
    Nat.card {z : X × Y // P z.1 z.2} * m ≤ Nat.card X * M := by
  classical
  letI : Fintype X := Fintype.ofFinite _
  let s (x : X) := {y : Y // P x y}
  let e : {z : X × Y // P z.1 z.2} ≃ Σ x, s x :=
    { toFun := fun z => ⟨z.val.1, ⟨z.val.2, z.property⟩⟩
      invFun := fun z => ⟨(z.1, z.2.val), z.2.property⟩
      left_inv := by rintro ⟨⟨x, y⟩, hxy⟩; rfl
      right_inv := by rintro ⟨x, ⟨y, hxy⟩⟩; rfl }
  rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_mul, Nat.card_eq_fintype_card (α := X)]
  calc
    _ ≤ ∑ _x : X, M := Finset.sum_le_sum fun x _ => h x
    _ = _ := by simp [nsmul_eq_mul]

private theorem card_filter_mono {X : Type*} [Finite X] {P Q : X → Prop}
    (h : ∀ x, P x → Q x) : Nat.card {x : X // P x} ≤ Nat.card {x : X // Q x} :=
  Nat.card_le_card_of_injective (fun x => (⟨x.val, h x.val x.property⟩ : {x : X // Q x}))
    (fun _ _ he => Subtype.ext (congrArg (fun y : {x : X // Q x} => y.val) he))

/-- Any X-bad event keeps its probability in the joint sample. -/
theorem card_joint_x_bad_le (p : BW n) (a b : ℕ) (P : XCheckSample p a → Prop)
    (m : ℕ) (h : Nat.card {G : XCheckSample p a // P G} * m ≤ Nat.card (XCheckSample p a)) :
    Nat.card {z : CSSJointSample p a b // P z.1} * m ≤ Nat.card (CSSJointSample p a b) := by
  rw [card_prod_leftPredicate, Nat.card_prod, mul_right_comm]
  exact Nat.mul_le_mul_right _ h

/-- A conditional event may depend on the X-space and its chosen Z-coordinate basis. -/
def jointConditionalEvent (p : BW n) (a b : ℕ)
    (P : (H : Submodule CSSBit (BW n)) → (Fin b → cssOrthogonal H) → Prop)
    (z : CSSJointSample p a b) : Prop :=
  ∃ hH : Module.finrank CSSBit (columnsToWord z.1).range = a,
    P (columnsToWord z.1).range (zSampleEquiv _ hH b z.2)

theorem card_joint_conditional_le (p : BW n) (a b : ℕ)
    (P : (H : Submodule CSSBit (BW n)) → (Fin b → cssOrthogonal H) → Prop) (m C : ℕ)
    (hP : ∀ G : XCheckSample p a, let H := (columnsToWord G).range
      Module.finrank CSSBit H = a →
        Nat.card {D : Fin b → cssOrthogonal H // P H D} * m ≤
          C * Nat.card (ZCheckCoefficients n a b)) :
    Nat.card {z : CSSJointSample p a b // jointConditionalEvent p a b P z} * m ≤
      C * Nat.card (CSSJointSample p a b) := by
  have hb (G : XCheckSample p a) :
      Nat.card {D : ZCheckCoefficients n a b // jointConditionalEvent p a b P (G, D)} * m ≤
        C * Nat.card (ZCheckCoefficients n a b) := by
    classical
    let H := (columnsToWord G).range
    by_cases hH : Module.finrank CSSBit H = a
    · have he (D : ZCheckCoefficients n a b) :
          jointConditionalEvent p a b P (G, D) ↔ P H (zSampleEquiv H hH b D) := by
        constructor
        · rintro ⟨h, hh⟩
          exact hh
        · exact fun hh => ⟨hH, hh⟩
      rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_zCoefficients_predicate_eq]
      exact hP G hH
    · letI : IsEmpty {D : ZCheckCoefficients n a b // jointConditionalEvent p a b P (G, D)} :=
        ⟨fun D => hH D.property.choose⟩
      simp
  have h := card_prod_predicate_bound (fun G D => jointConditionalEvent p a b P (G, D))
    m (C * Nat.card (ZCheckCoefficients n a b)) hb
  rw [Nat.card_prod]
  exact h.trans_eq (by ring)

theorem zSample_card_eq_coefficients (H : Submodule CSSBit (BW n))
    (hH : Module.finrank CSSBit H = a) (b : ℕ) :
    Nat.card (Fin b → cssOrthogonal H) = Nat.card (ZCheckCoefficients n a b) :=
  (Nat.card_congr (zSampleEquiv H hH b)).symm

/-- Full-rank X samples together with Z samples whose span contains the
image of the X space under a specified binary matrix. -/
def jointSymmetricBad (p : BW n) (a b : ℕ) (Q : Matrix (Fin n) (Fin n) CSSBit)
    (z : CSSJointSample p a b) : Prop :=
  jointConditionalEvent p a b
    (fun H D => H.map Q.mulVecLin ≤ (zColumnsToWord H D).range) z

theorem card_jointSymmetricBad_rank_le (p : BW n) (a b : ℕ)
    (Q : Matrix (Fin n) (Fin n) CSSBit) (ha : a ≤ n)
    (hcodim : 2 * n ≤ 5 * (n - a - b)) :
    Nat.card {z : CSSJointSample p a b // jointSymmetricBad p a b Q z} *
        2 ^ (plantedRank Q p * a / 10) ≤ 2 * Nat.card (CSSJointSample p a b) := by
  let r := plantedRank Q p
  let Lo (z : CSSJointSample p a b) :=
    columnFinrank a (plantedImageColumns Q p z.1) ≤ min r a / 4
  let Hi : (H : Submodule CSSBit (BW n)) → (Fin b → cssOrthogonal H) → Prop :=
    fun H D => min r a / 4 < Module.finrank CSSBit (H.map Q.mulVecLin) ∧
      H.map Q.mulVecLin ≤ (zColumnsToWord H D).range
  let High (z : CSSJointSample p a b) := jointConditionalEvent p a b Hi z
  have hinc (z : CSSJointSample p a b) (hz : jointSymmetricBad p a b Q z) : Lo z ∨ High z := by
    by_cases hLo : Lo z
    · exact Or.inl hLo
    · obtain ⟨hH, hD⟩ := hz
      have h := Nat.lt_of_not_ge hLo
      change min r a / 4 < columnFinrank a (plantedImageColumns Q p z.1) at h
      rw [plantedImageColumns_finrank_eq] at h
      exact Or.inr ⟨hH, h, hD⟩
  have hlo : Nat.card {z : CSSJointSample p a b // Lo z} * 2 ^ (r * a / 10) ≤
      Nat.card (CSSJointSample p a b) :=
    card_joint_x_bad_le p a b _ _ (card_plantedQ_low_image_rank_normalized Q p a)
  have hr : r ≤ n := (Submodule.finrank_le (plantedRestriction Q p).range).trans_eq
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
  have hhi : Nat.card {z : CSSJointSample p a b // High z} * 2 ^ (r * a / 10) ≤
      Nat.card (CSSJointSample p a b) := by
    have h := card_joint_conditional_le p a b Hi (2 ^ (r * a / 10)) 1 (by
      intro G H hH
      let L := H.map Q.mulVecLin
      by_cases h : min r a / 4 < Module.finrank CSSBit L
      · have hc : 2 * n ≤ 5 * (Module.finrank CSSBit (cssOrthogonal H) - b) := by
          rw [cssOrthogonal_finrank, show Module.finrank CSSBit H = a from hH]
          exact hcodim
        simpa only [Hi, H, L, h, true_and, one_mul, zSample_card_eq_coefficients H hH b] using
          card_zSamples_containing_image_normalized H L a b r hr ha h hc
      · letI : IsEmpty {D : Fin b → cssOrthogonal H // Hi H D} := ⟨fun D => h D.property.1⟩
        simp)
    simpa only [one_mul] using h
  have hcard := (card_filter_mono hinc).trans (card_predicate_or_le Lo High)
  calc
    _ ≤ (Nat.card {z : CSSJointSample p a b // Lo z} +
        Nat.card {z : CSSJointSample p a b // High z}) * 2 ^ (r * a / 10) :=
      Nat.mul_le_mul_right _ hcard
    _ ≤ _ := by rw [add_mul, two_mul]; exact Nat.add_le_add hlo hhi

theorem card_jointSymmetricBad_rows_le (p : BW n) (a b w : ℕ)
    (ha : a ≤ n) (hcodim : 2 * n ≤ 5 * (n - a - b)) (hw : 0 < w)
    (hp : w < wordWeight p) (Q : Matrix (Fin n) (Fin n) CSSBit)
    (hQ : Q ≠ 0) (hs : Q.IsSymm) (hrow : ∀ i, wordWeight (Q.row i) ≤ w) :
    Nat.card {z : CSSJointSample p a b // jointSymmetricBad p a b Q z} *
      2 ^ ((nonzeroRows Q).card * a / (20 * w)) ≤ 2 * Nat.card (CSSJointSample p a b) := by
  have hr := nonzeroRows_card_le_twice_sparse_plantedRank Q p w hs hQ hrow hp
  have hExp := normalized_symmetric_penalty_mono _ w _ a hw hr
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hExp)).trans
    (card_jointSymmetricBad_rank_le p a b Q ha hcodim)

theorem exists_good_CSSJointSample (p : BW n) (a b : ℕ)
    (xBad : XCheckSample p a → Prop)
    (zBad : (H : Submodule CSSBit (BW n)) → (Fin b → cssOrthogonal H) → Prop)
    (qBad : CSSJointSample p a b → Prop)
    (fullRank : ∀ G, ¬ xBad G → Module.finrank CSSBit (columnsToWord G).range = a)
    (hcount : Nat.card {z : CSSJointSample p a b // xBad z.1} +
      Nat.card {z : CSSJointSample p a b // jointConditionalEvent p a b zBad z} +
      Nat.card {z : CSSJointSample p a b // qBad z} < Nat.card (CSSJointSample p a b)) :
    ∃ (G : XCheckSample p a) (D : ZCheckCoefficients n a b)
      (hH : Module.finrank CSSBit (columnsToWord G).range = a),
      ¬ xBad G ∧ ¬ zBad (columnsToWord G).range (zSampleEquiv _ hH b D) ∧ ¬ qBad (G, D) := by
  classical
  let X := CSSJointSample p a b
  letI : Fintype X := Fintype.ofFinite _
  let P (z : X) := xBad z.1
  let Z (z : X) := jointConditionalEvent p a b zBad z
  let U := Finset.univ.filter fun z : X => (P z ∨ Z z) ∨ qBad z
  have hc := (card_predicate_or_le (fun x => P x ∨ Z x) qBad).trans
    (Nat.add_le_add_right (card_predicate_or_le P Z) _)
  have hlt := hc.trans_lt hcount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card,
    ← Finset.card_univ] at hlt
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (show U.card < _ from hlt)
  have h : ¬ ((P z ∨ Z z) ∨ qBad z) := fun he =>
    hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  have hx : ¬ xBad z.1 := fun he => h (Or.inl (Or.inl he))
  refine ⟨z.1, z.2, fullRank z.1 hx, hx, ?_, fun he => h (Or.inr he)⟩
  exact fun he => h (Or.inl (Or.inr ⟨fullRank z.1 hx, he⟩))

#print axioms card_joint_x_bad_le
#print axioms card_joint_conditional_le
#print axioms card_jointSymmetricBad_rows_le
#print axioms exists_good_CSSJointSample

end
end CriticalDepth.Manuscript20261114.CSSCheckSpaces
