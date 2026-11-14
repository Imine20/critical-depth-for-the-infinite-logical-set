import CSSRigidityCheckSpaces
import CSSBinaryMonomial
import CSSPhysicalRangePreservation
import CSSConcreteMonomial
import CSSPhaseGraph
import CSSPhaseRigidity
import CSSPauliMonomial
import FaultSupportPreserving
import FaultOnSiteSupport

/-!
# CSS rigidity and the upper fault-exponent envelope
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.FaultCircuitSupport CriticalDepth.FaultNativeModel CriticalDepth.FaultSupportPreserving
open scoped ENat Matrix

variable {n : ℕ}

theorem kernel_iff_cssOrthogonal_of_check_rows
    {b : ℕ} (J : Submodule CSSBit (CSSWord n)) (B : Matrix (Fin b) (Fin n) CSSBit)
    (hB : ∀ w : CSSWord n, w ∈ J ↔ ∃ a : Fin b → CSSBit, a ᵥ* B = w)
    (w : CSSWord n) : B *ᵥ w = 0 ↔ w ∈ cssOrthogonal J := by
  rw [cssOrthogonal_mem]
  constructor
  · intro h v hv
    obtain ⟨a, rfl⟩ := (hB v).mp hv
    rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, h, dotProduct_zero]
  · intro h
    funext i
    have hi : (fun j => B i j) ∈ J := (hB _).mpr ⟨Pi.single i 1, Matrix.single_one_vecMul i B⟩
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct_comm]
    exact h _ hi

/-- Every exact shallow physical circuit is a scalar multiple of a tensor Pauli. -/
theorem physicalCSS_exactCircuit_tensorPauli

    (H J : Submodule CSSBit (CSSWord n)) (q R : ℕ) (hq : 1 ≤ q) (hRpos : 1 ≤ R)
    (S : RigidityCheckSpaces H J R)
    (B : Matrix (Fin (Module.finrank CSSBit J)) (Fin n) CSSBit)
    (hRows : Function.Injective (fun a : Fin (Module.finrank CSSBit J) → CSSBit => a ᵥ* B))
    (hB : ∀ w : CSSWord n, w ∈ J ↔ ∃ a : Fin (Module.finrank CSSBit J) → CSSBit, a ᵥ* B = w)
    (L : Layers n q) (hdepth : q ^ L.length ≤ R)
    (W : Operator (Fin (2 ^ cssLogicalQubits H J)))
    (hW : Implements (physicalCSSCode H J S.compatible) (layerSequenceEval L) W) :
    ∃ (x z : CSSWord n) (phase : ℂˣ), star (phase : ℂ) * (phase : ℂ) = 1 ∧
      layerSequenceEval L = (phase : ℂ) •
        tensorEntries (fun i => (cssXWord x i).matrix * (cssZWord z i).matrix) := by
  classical
  let U := layerSequenceEval L
  let D := Module.finrank CSSBit H + 1
  let b := Module.finrank CSSBit J
  let cutoff := max (R * D) ((b + 1) * (R + 1) + R)
  have hD : 2 ≤ D := by have := S.xDimension; omega
  have hRD : R ≤ R * D := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hU : IsUnitary U := layerSequenceEval_isUnitary L
  obtain ⟨f, u, hunit, hform⟩ := physicalCSS_exactCircuit_monomial H J S.compatible
    q R hq (fun v hv hn => hRD.trans_lt (S.xDistance v hv hn))
    S.xDistance (fun v hv hn => (le_max_left _ _).trans_lt (S.zDistance v hv hn))
    S.zDualDistance L hdepth W hW
  obtain ⟨p, v, hm, hvunit⟩ := exists_binaryMonomial_of_basis_form U f u hunit hform
  obtain ⟨hCoset, hPhase⟩ := binaryMonomial_implements_preserves_cosets H J S.compatible hm hW
  let rows (i : Fin n) := layerSequenceCone (L.reverse.map Layer.adjoint) {i}
  let cols (i : Fin n) := layerSequenceCone L {i}
  have hrows : ∀ i : Fin n, (rows i).card ≤ R := by
    intro i
    have h := layerSequenceCone_card_le (L.reverse.map Layer.adjoint) {i} hq
    exact (by simpa [rows] using h : (rows i).card ≤ q ^ L.length).trans hdepth
  have hcols : ∀ i : Fin n, (cols i).card ≤ R := by
    intro i
    have h := layerSequenceCone_card_le L {i} hq
    exact (by simpa [cols] using h : (cols i).card ≤ q ^ L.length).trans hdepth
  have hrow (i : Fin n) :
      SupportedOn (propagate U.conjTranspose (pauliMatrix 0 (singleSitePauli i .Z))) (rows i) := by
    change SupportedOn (propagate (layerSequenceEval L).conjTranspose _) _
    rw [← Matrix.star_eq_conjTranspose, ← layerSequenceEval_reverse_adjoint]
    exact layerSequence_conjugate_supportedOn _ {i}
      (singleSitePauli_supportedOn {i} i (by simp) .Z)
  have hcol (i : Fin n) :
      SupportedOn (propagate U (pauliMatrix 0 (singleSitePauli i .X))) (cols i) :=
    layerSequence_conjugate_supportedOn L {i} (singleSitePauli_supportedOn {i} i (by simp) .X)
  have hp : ∀ x, p x = x + p 0 := by
    apply permutation_eq_translation_of_sparse_exclusion H (cssOrthogonal J) R D hD
      (cssShortOrthogonalityTests H) ?_ ?_ ?_ p p.bijective rows cols hrows hcols
      (fun i => monomial_permutation_dependsOn hU hm i (rows i) (hrow i))
      (fun j => monomial_bitDifference_zero_of_outside hU hm j (cols j) (hcol j))
      hCoset S.linearExclusion
    · intro x hx hxH
      exact (Nat.lt_succ_self _).trans (S.xDualDistance x ((cssOrthogonal_mem H x).mpr hxH) hx)
    · intro x hx hxL
      have h := (cssOrthogonal_mem (cssOrthogonal J) x).mpr hxL
      rw [cssOrthogonal_involutive] at h
      exact (le_max_left _ _).trans_lt (S.zDistance x h hx)
    · intro x hx hle
      by_contra h
      exact (not_le_of_gt (S.xDistance x hx h)) hle
  have hloc (i : Fin n) : DependsOn (cols i) (bitPhaseDifference v i) :=
    (monomial_translate_phaseDifference_dependsOn hU hm (p 0) hp i (cols i) (hcol i)).2
  have hInv : ∀ a ∈ H, ∀ x ∈ cssOrthogonal J, phaseDifference a v x = 1 := by
    intro a ha x hx
    simp [phaseDifference, hPhase a ha x hx]
  have hL (i : Finset (Fin n)) (hi : i.card ≤ R) :
      ∀ x : CSSWord n, ∃ y ∈ cssOrthogonal J, ∀ j ∈ i, y j = x j :=
    S.allowedProjection i (hi.trans hRD)
  have hcut : (b + 1) * (R + 1) + R ≤ cutoff := le_max_right _ _
  have hT₁ : R + 2 ≤ cutoff := by
    have h : 1 * (R + 1) ≤ (b + 1) * (R + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hT₂ : 1 + (b + 1) * (R + 1) ≤ cutoff := by omega
  have hdB : ∀ w : CSSWord n, w ≠ 0 → (∃ a : Fin b → CSSBit, a ᵥ* B = w) →
      cutoff < wordWeight w := fun w hw h => S.zDistance w ((hB w).mpr h) hw
  have hMixed := mixedBitPhaseDifference_constant_of_short_light_cones H (cssOrthogonal J) B
    hRows (fun w => (kernel_iff_cssOrthogonal_of_check_rows J B hB w).mp)
    R cutoff hT₁ hT₂ hdB v S.xProjection hL hInv
    (fun i => ⟨cols i, hcols i, hloc i⟩)
  have hQ : ∀ i, wordWeight (fun j => mixedPhaseMatrix v i j) ≤ R := by
    intro i
    refine (wordWeight_le_of_supported (S := cols i) ?_).trans (hcols i)
    intro j hj
    by_cases hij : i = j
    · subst j
      simp [mixedPhaseMatrix]
    · apply (mixedPhaseMatrix_eq_zero_iff v i j hij).mpr
      by_contra hn
      exact hj (phaseNeighbors_le_of_dependence v i (cols i) (hloc i)
        ((phaseNeighbors_mem_iff v i j).mpr ⟨hij, 0, hn⟩))
  obtain ⟨z, hz⟩ := phase_is_Pauli_of_sparse_symmetric_exclusion_of_check_rows H J v hMixed
    hQ hInv (fun s hs => S.xProjection s (hs.trans hRpos)) B hRows hB
    (fun w hw hn => by
      have hp : (b + 1) * 1 ≤ (b + 1) * (R + 1) := Nat.mul_le_mul_left _ (by omega)
      exact (by omega : b + 1 ≤ cutoff).trans_lt (S.zDistance w hw hn))
    S.symmetricExclusion
  refine ⟨p 0, z, v 0, ?_, ?_⟩
  · exact hvunit 0
  · apply monomialTranslation_eq_smul_tensorPauli U (p 0) z (v 0)
    intro x y
    let x' := binaryWordEquiv n x
    let y' := binaryWordEquiv n y
    have hf := hp y'
    have hz' := congrArg (fun w : ℂˣ => (w : ℂ)) (hz y')
    have he := hm x' y'
    rw [hf, hz', Units.val_mul] at he
    dsimp only [x', y'] at he
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at he

theorem physicalCSS_exactCircuit_preservesSupports
    (H J : Submodule CSSBit (CSSWord n)) (q R : ℕ) (hq : 1 ≤ q) (hRpos : 1 ≤ R)
    (S : RigidityCheckSpaces H J R)
    (B : Matrix (Fin (Module.finrank CSSBit J)) (Fin n) CSSBit)
    (hRows : Function.Injective (fun a : Fin (Module.finrank CSSBit J) → CSSBit => a ᵥ* B))
    (hB : ∀ w : CSSWord n, w ∈ J ↔ ∃ a : Fin (Module.finrank CSSBit J) → CSSBit, a ᵥ* B = w)
    (L : Layers n q) (hdepth : q ^ L.length ≤ R)
    (W : Operator (Fin (2 ^ cssLogicalQubits H J)))
    (hW : Implements (physicalCSSCode H J S.compatible) (layerSequenceEval L) W) :
    PreservesSupports (layerSequenceEval L) := by
  obtain ⟨x, z, phase, _, hform⟩ :=
    physicalCSS_exactCircuit_tensorPauli H J q R hq hRpos S B hRows hB L hdepth W hW
  rw [hform]
  apply preservesSupports_smul
  apply preservesSupports_tensorEntries
  intro i
  exact isUnitary_mul (singlePauli_isUnitary (cssXWord x i))
    (singlePauli_isUnitary (cssZWord z i))

#print axioms physicalCSS_exactCircuit_tensorPauli
#print axioms physicalCSS_exactCircuit_preservesSupports

end CriticalDepth.Manuscript20261114.CSSCheckSpaces