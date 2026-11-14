import CSSWeightBallCounts

/-!
Full-rank planted X checks with the required distance conditions.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

noncomputable section

abbrev PlantedColumnSpace {n : ℕ} (p : BW n) := (bitFunctional p).ker

def columnsToWord {n a : ℕ} {p : BW n} (G : Fin a → PlantedColumnSpace p) :
    (Fin a → ZMod 2) →ₗ[ZMod 2] BW n where
  toFun y := ∑ i, y i • (G i).val
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' k y := by simp [Finset.smul_sum, smul_smul]

theorem dotProduct_range_columnsToWord_iff {n a : ℕ} {p v : BW n}
    (G : Fin a → PlantedColumnSpace p) :
    v ∈ cssOrthogonal (columnsToWord G).range ↔
      ∀ i, dotProduct v (G i).val = 0 := by
  constructor
  · intro h i
    let y : Fin a → ZMod 2 := Pi.single i 1
    have hmem : (G i).val ∈ (columnsToWord G).range := ⟨y, by
      change (∑ j, y j • (G j).val) = _
      dsimp only [y]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp⟩
    exact (cssOrthogonal_mem _ _).mp h _ hmem
  · intro h
    rw [cssOrthogonal_mem]
    rintro _ ⟨y, rfl⟩
    change dotProduct v (∑ i, y i • (G i).val) = 0
    rw [dotProduct_sum]
    exact Finset.sum_eq_zero fun i _ => by simp [dotProduct_smul, h]

theorem columnsToWord_range_le_planted {n a : ℕ} {p : BW n}
    (G : Fin a → PlantedColumnSpace p) :
    (columnsToWord G).range ≤ (bitFunctional p).ker := by
  rintro _ ⟨y, rfl⟩
  show bitFunctional p (∑ i, y i • (G i).val) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by
    have h : bitFunctional p (G j).val = 0 := (G j).property
    rw [map_smul, h, smul_zero]

/-- Rank failure, short nonzero combinations, and an unexpected short dual word. -/
def badXCheckSample {n a : ℕ} (p : BW n) (d w : ℕ) (G : Fin a → PlantedColumnSpace p) : Prop :=
  (∃ y : Fin a → CSSBit, y ≠ 0 ∧ wordWeight (columnsToWord G y) ≤ w) ∨
    ∃ v : BW n, wordWeight v ≤ d ∧ v ≠ 0 ∧ v ≠ p ∧
      v ∈ cssOrthogonal (columnsToWord G).range

theorem good_xChecks_of_not_bad {n a d w : ℕ} (p : BW n) (hp : wordWeight p = d)
    (G : Fin a → PlantedColumnSpace p) (hG : ¬ badXCheckSample p d w G) :
    let H := (columnsToWord G).range
    Function.Injective (columnsToWord G) ∧ Module.finrank CSSBit H = a ∧
      p ∈ cssOrthogonal H ∧ (∀ x ∈ H, x ≠ 0 → w < wordWeight x) ∧
      ∀ v ∈ cssOrthogonal H, v ≠ 0 → d ≤ wordWeight v := by
  let M := columnsToWord G
  have hsmall (y : Fin a → CSSBit) (hy : y ≠ 0) : w < wordWeight (M y) := by
    by_contra! hh
    exact hG (Or.inl ⟨y, hy, hh⟩)
  have hinj : Function.Injective M := by
    intro y y' hy
    by_contra hne
    have ht := hsmall (y - y') (sub_ne_zero.mpr hne)
    rw [map_sub, hy, sub_self] at ht
    simp [wordWeight] at ht
  refine ⟨hinj, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · apply (dotProduct_range_columnsToWord_iff G).mpr
    intro i
    exact (G i).property
  · rintro _ ⟨y, rfl⟩ hy
    exact hsmall y (fun h => hy (h ▸ M.map_zero))
  · intro v hv hv0
    by_contra! hdv
    have hvp : v ≠ p := fun h => by rw [h, hp] at hdv; omega
    exact hG (Or.inr ⟨v, hdv.le, hv0, hvp, hv⟩)

theorem card_bad_xChecks_le {n a d w : ℕ} (p : BW n) :
    letI : Fintype (PlantedColumnSpace p) := Fintype.ofFinite _
    let N := Fintype.card (PlantedColumnSpace p)
    Nat.card {G : Fin a → PlantedColumnSpace p // badXCheckSample p d w G} ≤
      (2 ^ a - 1) * natShells n w * N ^ (a - 1) + natShells n d * (N ^ a / 2 ^ a) := by
  classical
  let V := PlantedColumnSpace p
  letI : Fintype V := Fintype.ofFinite _
  let N := Fintype.card V
  let X := Fin a → V
  change Nat.card {G : X // badXCheckSample p d w G} ≤ _
  let low : Finset V := Finset.univ.filter fun x => wordWeight (x : BW n) ≤ w
  have hlow : low.card ≤ natShells n w := by
    have h := Finset.card_le_card_of_injOn (f := fun x : V => x.val)
      (s := low) (t := Finset.univ.filter fun v : BW n => wordWeight v ≤ w)
      (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
      (fun _ _ _ _ h => Subtype.ext h)
    exact h.trans (card_binary_atMost_le n w)
  let coeff : Finset (Fin a → CSSBit) := Finset.univ.erase 0
  have hCoeff : coeff.card = 2 ^ a - 1 := by
    simp [coeff, Finset.card_erase_of_mem, Fintype.card_fun, ZMod.card, CSSBit]
  let dual : Finset (BW n) := Finset.univ.filter fun v => wordWeight v ≤ d ∧ v ≠ 0 ∧ v ≠ p
  have hdual : dual.card ≤ natShells n d := by
    apply le_trans _ (card_binary_atMost_le n d)
    exact Finset.card_le_card (fun _ h =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.1⟩)
  let badX (y : Fin a → CSSBit) : Finset X :=
    Finset.univ.filter fun G => (∑ j, y j • G j) ∈ low
  let badD (v : BW n) : Finset X :=
    Finset.univ.filter fun G => ∀ j, dotProduct v (G j).val = 0
  have hbadX (y) (hy : y ∈ coeff) : (badX y).card ≤ natShells n w * N ^ (a - 1) := by
    have he := card_linearCombination_bad_le y (Finset.ne_of_mem_erase hy) low
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at he
    rw [Fintype.card_fin] at he
    exact he.trans (Nat.mul_le_mul_right _ hlow)
  have hbadD (v) (hv : v ∈ dual) : (badD v).card ≤ N ^ a / 2 ^ a := by
    obtain ⟨_, hn, hvp⟩ := (Finset.mem_filter.mp hv).2
    have hd := card_planted_columns_all_orthogonal p v hn hvp a
    change Nat.card {G : Fin a → V // ∀ j, dotProduct v (G j).val = 0} * 2 ^ a = N ^ a at hd
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hd
    change (badD v).card * 2 ^ a = N ^ a at hd
    rw [← hd, Nat.mul_div_cancel _ (by positivity)]
  have hsX := (Finset.card_biUnion_le (s := coeff) (t := badX)).trans
    (Finset.sum_le_sum hbadX)
  have hsD := (Finset.card_biUnion_le (s := dual) (t := badD)).trans
    (Finset.sum_le_sum hbadD)
  simp only [Finset.sum_const, nsmul_eq_mul, hCoeff, ← mul_assoc] at hsX
  simp only [Finset.sum_const, nsmul_eq_mul] at hsD
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsubset : (Finset.univ.filter fun G : X => badXCheckSample p d w G) ⊆
      (coeff.biUnion badX) ∪ (dual.biUnion badD) := by
    intro G hG
    rcases (Finset.mem_filter.mp hG).2 with ⟨y, hy, hwt⟩ | ⟨v, hwt, hv, hvp, horth⟩
    · apply Finset.mem_union_left
      refine Finset.mem_biUnion.mpr ⟨y, by simp [coeff, hy], ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa only [Submodule.coe_sum, Submodule.coe_smul, columnsToWord, LinearMap.coe_mk,
        AddHom.coe_mk] using hwt
    · apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwt, hv, hvp⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (dotProduct_range_columnsToWord_iff G).mp horth⟩
  exact (Finset.card_le_card hsubset).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hsX
    (hsD.trans (Nat.mul_le_mul_right _ hdual))))

theorem card_planted_columnSpace {n : ℕ} (p : BW n) (hp : p ≠ 0) :
    Nat.card (PlantedColumnSpace p) = 2 ^ (n - 1) := by
  classical
  have hp' : bitFunctional p ≠ 0 := fun h =>
    hp ((dotProductEquiv (ZMod 2) (Fin n)).injective (by simpa [bitFunctional] using h))
  have hr : (bitFunctional p).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    have hex : ∃ x, bitFunctional p x ≠ 0 := by
      by_contra! h
      exact hp' (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hex
    have ho : bitFunctional p x = 1 := by
      rcases (show ∀ y : CSSBit, y = 0 ∨ y = 1 by decide) (bitFunctional p x) with h | h
      · exact (hx h).elim
      · exact h
    intro c
    exact ⟨c • x, by simp [map_smul, ho]⟩
  have hdim := (bitFunctional p).finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hdim
  have hd : Module.finrank CSSBit (PlantedColumnSpace p) = n - 1 := by
    change 1 + Module.finrank CSSBit (PlantedColumnSpace p) = n at hdim
    omega
  letI : Fintype (PlantedColumnSpace p) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := CSSBit), ZMod.card, hd]

#print axioms good_xChecks_of_not_bad
#print axioms card_bad_xChecks_le
#print axioms card_planted_columnSpace

end

end CriticalDepth.Manuscript20261114.CSSCheckSpaces