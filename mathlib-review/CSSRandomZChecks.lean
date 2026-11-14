import CSSRandomXChecks

/-!
Independent sampling of the Z-check generators inside the orthogonal of
the X-check space. A nonzero short coefficient combination tests primal
distance and includes rank failure. An unexpected short dual word tests
one nonzero linear functional on all sampled columns.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

noncomputable section

variable {n b : ℕ}

def zColumnsToWord (H : Submodule CSSBit (BW n))
    (G : Fin b → cssOrthogonal H) : (Fin b → CSSBit) →ₗ[CSSBit] BW n :=
  (cssOrthogonal H).subtype.comp
    ((LinearEquiv.piRing CSSBit (cssOrthogonal H) (Fin b) CSSBit).symm G)

theorem zColumnsToWord_apply (H : Submodule CSSBit (BW n))
    (G : Fin b → cssOrthogonal H) (y : Fin b → CSSBit) :
    zColumnsToWord H G y = ∑ j, y j • (G j).val := by
  simp only [zColumnsToWord, LinearMap.comp_apply, LinearEquiv.piRing_symm_apply,
    Submodule.subtype_apply, Submodule.coe_sum, Submodule.coe_smul]

theorem zColumnsToWord_range_le (H : Submodule CSSBit (BW n))
    (G : Fin b → cssOrthogonal H) : (zColumnsToWord H G).range ≤ cssOrthogonal H := by
  rintro _ ⟨y, rfl⟩
  exact (((LinearEquiv.piRing CSSBit (cssOrthogonal H) (Fin b) CSSBit).symm G) y).property

theorem mem_orthogonal_zColumnsToWord_iff (H : Submodule CSSBit (BW n))
    (G : Fin b → cssOrthogonal H) (v : BW n) :
    v ∈ cssOrthogonal (zColumnsToWord H G).range ↔
      ∀ i, dotProduct v (G i).val = 0 := by
  rw [cssOrthogonal_mem]
  constructor
  · intro h i
    have hmem : (G i).val ∈ (zColumnsToWord H G).range := ⟨Pi.single i 1, by
      rw [zColumnsToWord_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp⟩
    exact h _ hmem
  · rintro h _ ⟨y, rfl⟩
    rw [zColumnsToWord_apply, dotProduct_sum]
    exact Finset.sum_eq_zero fun i _ => by simp [dotProduct_smul, h]

/-- Sampling these bad events jointly deals with rank failure, short words
in the span, and unexpected short words in its orthogonal. -/
def badZCheckSample (H : Submodule CSSBit (BW n)) (T W : ℕ)
    (G : Fin b → cssOrthogonal H) : Prop :=
  (∃ y : Fin b → CSSBit, y ≠ 0 ∧ wordWeight (zColumnsToWord H G y) ≤ T) ∨
  ∃ v : BW n, v ≠ 0 ∧ wordWeight v ≤ W ∧
    v ∈ cssOrthogonal (zColumnsToWord H G).range

theorem good_zChecks_of_not_bad (H : Submodule CSSBit (BW n)) (T W : ℕ)
    (G : Fin b → cssOrthogonal H) (hG : ¬ badZCheckSample H T W G) :
    let J := (zColumnsToWord H G).range
    Module.finrank CSSBit J = b ∧ J ≤ cssOrthogonal H ∧
      (∀ x ∈ J, x ≠ 0 → T < wordWeight x) ∧
      (∀ x ∈ cssOrthogonal J, x ≠ 0 → W < wordWeight x) := by
  let M := zColumnsToWord H G
  have hsmall (y : Fin b → CSSBit) (hy : y ≠ 0) : T < wordWeight (M y) := by
    by_contra! h
    exact hG (Or.inl ⟨y, hy, h⟩)
  have hinj : Function.Injective M := by
    intro y y' he
    by_contra hne
    have h := hsmall (y - y') (sub_ne_zero.mpr hne)
    rw [map_sub, he, sub_self] at h
    simp [wordWeight] at h
  change Module.finrank CSSBit M.range = b ∧ M.range ≤ cssOrthogonal H ∧ _
  refine ⟨?_, zColumnsToWord_range_le H G, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · rintro _ ⟨y, rfl⟩ hy
    exact hsmall y (fun h => hy (h ▸ M.map_zero))
  · intro v hv hv0
    by_contra! hh
    exact hG (Or.inr ⟨v, hv0, hh, hv⟩)

/-- Unified bad cardinality for the Z-sample. The estimate counts samples
in the same independent-column space used for the symmetric exclusion. -/
theorem card_bad_zChecks_le (H : Submodule CSSBit (BW n)) (b T W : ℕ)
    (hH : ∀ x ∈ H, x ≠ 0 → W < wordWeight x) :
    letI : Fintype (cssOrthogonal H) := Fintype.ofFinite _
    let N := Fintype.card (cssOrthogonal H)
    Nat.card {G : Fin b → cssOrthogonal H // badZCheckSample H T W G} ≤
      (2 ^ b - 1) * natShells n T * N ^ (b - 1) +
        natShells n W * (N ^ b / 2 ^ b) := by
  classical
  let V := cssOrthogonal H
  letI : Fintype V := Fintype.ofFinite _
  let N := Fintype.card V
  let X := Fin b → V
  let low : Finset V := Finset.univ.filter fun x => wordWeight (x : BW n) ≤ T
  have hlow : low.card ≤ natShells n T := by
    have h := Finset.card_le_card_of_injOn (f := fun x : V => x.val)
      (s := low) (t := Finset.univ.filter fun v : BW n => wordWeight v ≤ T)
      (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
      (fun _ _ _ _ h => Subtype.ext h)
    exact h.trans (card_binary_atMost_le n T)
  let coeff : Finset (Fin b → CSSBit) := Finset.univ.erase 0
  have hCoeff : coeff.card = 2 ^ b - 1 := by
    simp [coeff, Finset.card_erase_of_mem, Fintype.card_fun, ZMod.card, CSSBit]
  let dual : Finset (BW n) := Finset.univ.filter fun v => wordWeight v ≤ W ∧ v ≠ 0
  have hdual : dual.card ≤ natShells n W :=
    (Finset.card_le_card (t := Finset.univ.filter fun v : BW n => wordWeight v ≤ W)
      (fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.1⟩)).trans
      (card_binary_atMost_le n W)
  let badPrimal (y : Fin b → CSSBit) : Finset X :=
    Finset.univ.filter fun G => (∑ j, y j • G j) ∈ low
  let badDual (v : BW n) : Finset X :=
    Finset.univ.filter fun G => ∀ j, dotProduct v (G j).val = 0
  have hbadPrimal (y) (hy : y ∈ coeff) :
      (badPrimal y).card ≤ natShells n T * N ^ (b - 1) := by
    have he := card_linearCombination_bad_le y (Finset.ne_of_mem_erase hy) low
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin] at he
    exact he.trans (Nat.mul_le_mul_right _ hlow)
  have hbadDual (v) (hv : v ∈ dual) : (badDual v).card ≤ N ^ b / 2 ^ b := by
    obtain ⟨hw, hv₀⟩ := (Finset.mem_filter.mp hv).2
    have hF : (bitFunctional v).comp V.subtype ≠ 0 := by
      intro h
      have hm : v ∈ cssOrthogonal V := by
        rw [cssOrthogonal_mem]
        intro x hx
        exact LinearMap.congr_fun h (⟨x, hx⟩ : V)
      rw [show V = cssOrthogonal H from rfl, cssOrthogonal_involutive] at hm
      exact (not_lt_of_ge hw) (hH v hm hv₀)
    have hd := card_binary_columns_annihilated ((bitFunctional v).comp V.subtype) hF b
    change Nat.card {G : X // ∀ j, dotProduct v (G j).val = 0} * 2 ^ b = N ^ b at hd
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hd
    change (badDual v).card * 2 ^ b = N ^ b at hd
    rw [← hd, Nat.mul_div_cancel _ (by positivity)]
  have hp := (Finset.card_biUnion_le (s := coeff) (t := badPrimal)).trans
    (Finset.sum_le_sum hbadPrimal)
  have hd := (Finset.card_biUnion_le (s := dual) (t := badDual)).trans
    (Finset.sum_le_sum hbadDual)
  simp only [Finset.sum_const, nsmul_eq_mul, hCoeff, ← mul_assoc] at hp
  simp only [Finset.sum_const, nsmul_eq_mul] at hd
  have hsubset : (Finset.univ.filter fun G : X => badZCheckSample H T W G) ⊆
      (coeff.biUnion badPrimal) ∪ (dual.biUnion badDual) := by
    intro G hG
    rcases (Finset.mem_filter.mp hG).2 with ⟨y, hy, hw⟩ | ⟨v, hv, hw, horth⟩
    · apply Finset.mem_union_left
      refine Finset.mem_biUnion.mpr ⟨y, by simp [coeff, hy], ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [zColumnsToWord_apply] at hw
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using hw
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hv⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_orthogonal_zColumnsToWord_iff H G v).mp horth⟩⟩
  change Nat.card {G : X // badZCheckSample H T W G} ≤ _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (Finset.card_le_card hsubset).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add hp (hd.trans (Nat.mul_le_mul_right _ hdual))))

#print axioms good_zChecks_of_not_bad
#print axioms card_bad_zChecks_le

end
end CriticalDepth.Manuscript20261114.CSSCheckSpaces
