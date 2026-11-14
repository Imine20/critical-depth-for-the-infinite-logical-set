import CSSZCentralizer

/-!
# Monomiality from the CSS stabilizer and short Z checks
-/

open scoped BigOperators Kronecker

namespace CriticalDepth.Manuscript20261114.CSSZConjugation

open CriticalDepth.Manuscript CriticalDepth.Manuscript20261114.CSSCheckSpaces
open CriticalDepth.Manuscript20261114.CSSPauliRestriction
open CriticalDepth.CSSMonomial CriticalDepth.ReviewV2

variable {n k ρ t R D : ℕ}

private def supportOfWord (v : BinaryWord (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => v i ≠ 0

private theorem zCheck_supported (v : BinaryWord (Fin n)) :
    SupportedOn (zCheck v) (supportOfWord v) := by
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  have h : v i = 0 := by simpa [supportOfWord] using hi
  simp [h]

private theorem zCheck_diagonal (v : BinaryWord (Fin n))
    (x y : QubitBasis n) (hxy : x ≠ y) : zCheck v x y = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  unfold zCheck
  rw [pauliMatrix_zero_eq_tensorEntries]
  change (∏ j, (if v j = 0 then SinglePauli.I else .Z).matrix (x j) (y j)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hv : v i = 0
  · simp [hv, SinglePauli.matrix, Matrix.one_apply_ne hi]
  · rw [ite_eq_right hv]
    have hz (a b : Fin 2) (hab : a ≠ b) : SinglePauli.Z.matrix a b = 0 := by
      fin_cases a <;> fin_cases b <;> simp_all [SinglePauli.matrix]
    exact hz (x i) (y i) hi

private theorem zCheck_commutes_singleSiteZ (v : BinaryWord (Fin n)) (i : Fin n) :
    zCheck v * pauliMatrix 0 (singleSitePauli i .Z) =
      pauliMatrix 0 (singleSitePauli i .Z) * zCheck v := by
  rw [singleSitePauli_z_eq_diagonal]
  ext x y
  classical
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hxy : x = y
  · subst y
    exact mul_comm _ _
  · rw [zCheck_diagonal v x y hxy, zero_mul, mul_zero]

/-- The algebra step of physical CSS rigidity. It uses the given check tests
as generators, the stabilizer support exclusion, and the short-word
classification of its centralizer. -/
theorem exists_monomial_of_css_check_structure
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hPauli : ∀ U ∈ S, IsPauli (U : Operator (QubitBasis n)))
    (hSpace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (H : Submodule (ZMod 2) (BinaryWord (Fin n)))
    (tests : ShortOrthogonalityTests H D)
    (hChecks : ∀ v ∈ tests.tests, ∃ F : Operator (Fin (2 ^ k) × Fin 1),
      zCheck v * C.encoding = C.encoding * F)
    (hDistH : ∀ v ∈ H, v ≠ 0 → R < wordWeight v)
    (hNoShortStabilizer : ∀ (A : Finset (Fin n)), A.card ≤ R * D →
      ∀ U ∈ S, SupportedOn (U : Operator (QubitBasis n)) A → U = 1)
    (hZLocalCentralizer : ∀ (A : Finset (Fin n)), A.card ≤ R * D →
      ∀ p : A → SinglePauli,
        (∀ U ∈ S, (U : Operator (QubitBasis n)) * pauliMatrix 0 (extendLocalPauli A p) =
          pauliMatrix 0 (extendLocalPauli A p) * (U : Operator (QubitBasis n))) →
        pauliMatrix 0 (extendLocalPauli A p) ∈ Algebra.adjoin ℂ (zCheck '' tests.tests))
    (L : List (Layer n (fun _ => 2) ρ)) (hρ : 1 ≤ ρ)
    (hR : ρ ^ L.length ≤ R)
    (W : Operator (Fin (2 ^ k))) (hW : Implements C (layerSequenceEval L) W) :
    ∃ (f : Equiv.Perm (QubitBasis n)) (phase : QubitBasis n → ℂ),
      (∀ j, star (phase j) * phase j = 1) ∧
      ∀ x j, layerSequenceEval L x j = if x = f j then phase j else 0 := by
  classical
  let U := layerSequenceEval L
  have hu : IsUnitary U := layerSequenceEval_isUnitary L
  let u : Matrix.unitaryGroup (QubitBasis n) ℂ :=
    ⟨U, (isUnitary_iff_mem_unitaryGroup (QubitBasis n) _).mp hu⟩
  let generators := zCheck '' tests.tests
  have hgen : ∀ A ∈ generators, U * A * U.conjTranspose ∈ Algebra.adjoin ℂ generators := by
    rintro _ ⟨v, hv, rfl⟩
    let A := layerSequenceCone L (supportOfWord v)
    have hs : A.card ≤ R * D := by
      apply (layerSequenceCone_card_le L (supportOfWord v) hρ).trans
      apply Nat.mul_le_mul hR
      have he : (supportOfWord v).card = wordWeight v := by
        unfold wordWeight
        congr 1
        ext i
        simp [supportOfWord]
      rw [he]
      exact tests.weight_le v hv
    have hSupp : SupportedOn (U * zCheck v * U.conjTranspose) A :=
      layerSequence_conjugate_supportedOn L _ (zCheck_supported v)
    obtain ⟨hWu, Z, hZu, hImpl⟩ := hW
    have hpres : ∃ Y : Operator (Fin (2 ^ k) × Fin 1),
        (U * zCheck v * U.conjTranspose) * C.encoding = C.encoding * Y := by
      obtain ⟨F, hF⟩ := hChecks v hv
      exact ⟨_, conjugation_preserves_encoded_space C U (zCheck v) hu (W ⊗ₖ Z) F
        (point_kronecker_isUnitary W Z hWu hZu) hImpl hF⟩
    obtain ⟨c, hc, hcent⟩ := exists_localPauli_expansion_centralizer C A S hPauli hSpace
      (hNoShortStabilizer A hs) (U * zCheck v * U.conjTranspose) hSupp hpres
    rw [hc]
    change (∑ p, c p • pauliMatrix 0 (extendLocalPauli A p)) ∈
      (Algebra.adjoin ℂ generators).toSubmodule
    apply Submodule.sum_mem
    intro p _
    by_cases hp : c p = 0
    · rw [hp, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (hZLocalCentralizer A hs p (hcent p hp))
  apply exists_monomial_of_singleSiteZ_conjugates U hu
  refine singleSiteZ_conjugates_diagonal u generators hgen ?_ R ?_ ?_
  · intro i A hA
    obtain ⟨v, _, rfl⟩ := hA
    exact zCheck_commutes_singleSiteZ v i
  · intro i
    refine ⟨layerSequenceCone L {i}, ?_, ?_⟩
    · exact (layerSequenceCone_card_le L {i} hρ).trans (by simpa using hR)
    · exact layerSequence_conjugate_supportedOn L {i}
        (singleSitePauli_supportedOn {i} i (Finset.mem_singleton_self i) .Z)
  · intro O A hA hSupp hComm x y hxy
    exact diagonal_of_supported_commutes_zChecks tests A
      (fun v hv hn => hA.trans_lt (hDistH v hv hn)) O hSupp
      (fun v hv => hComm (zCheck v) (Algebra.subset_adjoin ⟨v, hv, rfl⟩)) x y hxy

#print axioms exists_monomial_of_css_check_structure

end CriticalDepth.Manuscript20261114.CSSZConjugation
