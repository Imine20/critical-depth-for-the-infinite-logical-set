import CSSDegenerateDistance
import Q37PackedSignatures

/-!
The Q37 half-signature certificates establish the actual CSS distance seven.
-/

open scoped Matrix BigOperators

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.Manuscript20261114.CSSCheckSpaces

private theorem halfSignature_parity_eq_if_same
    (checks : List ℕ) (z : ℕ)
    (hLen : checks.length = 18)
    (hC : (List.range 8).all (parityConsistentBucket (signatureColumns checks z)) = true)
    (s t : Finset (Fin 37)) (hs : s.card ≤ 3) (ht : t.card ≤ 3)
    (h : (checkMatrix checks) *ᵥ maskWord s = (checkMatrix checks) *ᵥ maskWord t) :
    dotProduct (wordOfNatMask 37 z) (maskWord s) = dotProduct (wordOfNatMask 37 z) (maskWord t) := by
  have hLen₀ : (signatureColumns checks z).length = 37 := by simp [signatureColumns]
  have hs₀ : ((List.ofFn fun i : Fin 37 => decide (i ∈ s)).filter id).length ≤ 3 := by
    rw [length_filter_ofFn]
    simpa using hs
  have ht₀ : ((List.ofFn fun i : Fin 37 => decide (i ∈ t)).filter id).length ≤ 3 := by
    rw [length_filter_ofFn]
    simpa using ht
  have hpar := certificate_agrees_on_masked_halves hC
    (List.ofFn fun i : Fin 37 => decide (i ∈ s))
    (List.ofFn fun i : Fin 37 => decide (i ∈ t))
    (by simp [hLen₀]) (by simp [hLen₀]) hs₀ ht₀
    (halfSignatures_same_syndrome checks z s t h hLen)
    (halfSignature_syndrome_bound checks z s hLen)
  rw [← halfSignature_bit_zero, ← halfSignature_bit_zero, Nat.testBit_zero, Nat.testBit_zero]
  have hEq : halfSignature (signatureColumns checks z) s % 2 =
      halfSignature (signatureColumns checks z) t % 2 := hpar
  rw [hEq]

private theorem quiet_smallWord_dot_zero
    (checks : List ℕ) (z : ℕ) (hLen : checks.length = 18)
    (hC : (List.range 8).all (parityConsistentBucket (signatureColumns checks z)) = true)
    (x : Q37Word) (hweight : wordWeight x < 7) (hquiet : (checkMatrix checks) *ᵥ x = 0) :
    dotProduct (wordOfNatMask 37 z) x = 0 := by
  obtain ⟨s, t, hs, ht, _, hst⟩ := signedMask_split x hweight
  change x = maskWord s + maskWord t at hst
  rw [hst, Matrix.mulVec_add] at hquiet
  have hEq : (checkMatrix checks) *ᵥ maskWord s = (checkMatrix checks) *ᵥ maskWord t := by
    funext i
    have he := congrFun hquiet i
    change ((checkMatrix checks) *ᵥ maskWord s) i + ((checkMatrix checks) *ᵥ maskWord t) i = 0 at he
    exact (by decide : ∀ a b : Bit, a + b = 0 → a = b) _ _ he
  have hdot := halfSignature_parity_eq_if_same checks z hLen hC s t hs ht hEq
  rw [hst, dotProduct_add, hdot]
  exact (by decide : ∀ b : Bit, b + b = 0) _

private theorem ker_checks_of_orthogonal (rows : List ℕ) (x : Q37Word)
    (hx : x ∈ cssOrthogonal (checkMatrix rows).vecMulLinear.range) :
    (checkMatrix rows) *ᵥ x = 0 := by
  funext j
  have hrow : (checkMatrix rows).row j ∈ (checkMatrix rows).vecMulLinear.range := ⟨Pi.single j 1, by
    rw [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]⟩
  change dotProduct ((checkMatrix rows).row j) x = 0
  rw [dotProduct_comm]
  exact (cssOrthogonal_mem _ _).mp hx _ hrow

private theorem orthogonal_eq_check_sup (H J : Submodule CSSBit Q37Word)
    (hHJ : H ≤ cssOrthogonal J) (hH : Module.finrank CSSBit H = 18)
    (hJ : Module.finrank CSSBit J = 18) (a : Q37Word)
    (ha : a ∈ cssOrthogonal J) (han : a ∉ H) :
    cssOrthogonal J = H ⊔ Submodule.span CSSBit {a} := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact sup_le hHJ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ha))
  · rw [Submodule.finrank_sup_span_singleton han, hH, cssOrthogonal_finrank, hJ]
    try decide

private theorem mem_check_of_pairing_zero (H J : Submodule CSSBit Q37Word)
    (a b x : Q37Word) (h : cssOrthogonal J = H ⊔ Submodule.span CSSBit {a})
    (hb : b ∈ cssOrthogonal H) (hab : dotProduct b a = 1)
    (hx : x ∈ cssOrthogonal J) (hx' : dotProduct b x = 0) : x ∈ H := by
  rw [h, Submodule.mem_sup] at hx
  obtain ⟨v, hv, u, hu, hvu⟩ := hx
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [← hvu, dotProduct_add, dotProduct_smul, (cssOrthogonal_mem _ _).mp hb _ hv,
    hab, zero_add, smul_eq_mul, mul_one] at hx'
  rw [hx', zero_smul, add_zero] at hvu
  exact hvu ▸ hv

/-- Every low-weight quiet X mask is an X check. -/
theorem q37_small_X_mask_check (x : Q37Word) (hx : x ∈ cssOrthogonal q37ZChecks)
    (hw : wordWeight x < 7) : x ∈ q37XChecks := by
  have hzero : dotProduct q37LogicalZ x = 0 := by
    apply quiet_smallWord_dot_zero zChecks logicalZ zDual_certificate.1
    · rw [← xSignatureColumns_eq]
      exact x_half_signature_certificate
    · exact hw
    · exact ker_checks_of_orthogonal zChecks x hx
  exact mem_check_of_pairing_zero q37XChecks q37ZChecks q37LogicalX q37LogicalZ x
    (orthogonal_eq_check_sup _ _ q37ChecksCompatible q37XChecks_finrank q37ZChecks_finrank _
      q37LogicalX_in_dual q37LogicalX_not_check)
    q37LogicalZ_in_dual (by rw [dotProduct_comm, q37Logical_dot]) hx hzero

/-- Every low-weight quiet Z mask is a Z check. -/
theorem q37_small_Z_mask_check (x : Q37Word) (hx : x ∈ cssOrthogonal q37XChecks)
    (hw : wordWeight x < 7) : x ∈ q37ZChecks := by
  have hzero : dotProduct q37LogicalX x = 0 := by
    apply quiet_smallWord_dot_zero xChecks logicalX xDual_certificate.1
    · rw [← zSignatureColumns_eq]
      exact z_half_signature_certificate
    · exact hw
    · exact ker_checks_of_orthogonal xChecks x hx
  exact mem_check_of_pairing_zero q37ZChecks q37XChecks q37LogicalZ q37LogicalX x
    (orthogonal_eq_check_sup _ _ (cssChecksCompatible_symm.mp q37ChecksCompatible) q37ZChecks_finrank
      q37XChecks_finrank _ q37LogicalZ_in_dual q37LogicalZ_not_check)
    q37LogicalX_in_dual q37Logical_dot hx hzero

theorem q37LogicalZ_weight : wordWeight q37LogicalZ = 7 := by
  rw [← wordSupport_card]
  change (Finset.univ.filter (fun i : Fin 37 => wordOfNatMask 37 logicalZ i ≠ 0)).card = 7
  have hs : (Finset.univ.filter (fun i : Fin 37 => wordOfNatMask 37 logicalZ i ≠ 0)) =
      sitesOfNatMask 37 logicalZ := by
    ext i
    cases h : logicalZ.testBit i.val <;> simp [sitesOfNatMask, wordOfNatMask, h]
  rw [hs, card_sitesOfNatMask]
  exact css_and_logical_certificate.2.2.2.2.2

theorem q37Code_actualDistance : HasActualDistance q37Code 7 :=
  physicalCSSCode_hasActualDistance_of_low_dual_in_checks q37XChecks q37ZChecks q37ChecksCompatible
    (fun x hx hw => q37_small_X_mask_check x hx hw) (fun x hx hw => q37_small_Z_mask_check x hx hw)
    q37LogicalZ q37LogicalZ_in_dual q37LogicalZ_not_check q37LogicalZ_weight

#print axioms q37Code_actualDistance

end CriticalDepth.Q37BinaryData