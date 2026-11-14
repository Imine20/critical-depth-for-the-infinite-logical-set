import FaultStabilizerTrace
import PauliGroup

/-!
# Pauli expansion on a sparse CSS support

If a support contains no nonidentity stabilizer, distinct Pauli words on
it remain trace-orthogonal after restriction to the stabilizer code. A
code-preserving operator on that support can therefore have coefficients
only at Pauli words in the stabilizer centralizer.
-/

open scoped BigOperators

namespace CriticalDepth.Manuscript20261114.CSSPauliRestriction

open CriticalDepth.Manuscript CriticalDepth.FaultStabilizerTrace
open CriticalDepth.PauliGroup Matrix

variable {n k : ℕ}

private def onSupport (A : Finset (Fin n)) (p : A → SinglePauli) :
    Operator (QubitBasis n) :=
  pauliMatrix 0 (extendLocalPauli A p)

private theorem extendLocalPauli_injective (A : Finset (Fin n)) :
    Function.Injective (extendLocalPauli A) := by
  intro p q hpq
  funext i
  have h := congrFun hpq i.val
  simpa [extendLocalPauli, i.property] using h

theorem exists_supported_pauli_expansion (A : Finset (Fin n))
    (O : Operator (QubitBasis n)) (hO : SupportedOn O A) :
    ∃ c : (A → SinglePauli) → ℂ, O = ∑ p, c p • pauliMatrix 0 (extendLocalPauli A p) := by
  classical
  obtain ⟨M, hM⟩ := hO
  have hspan : M ∈ Submodule.span ℂ (Set.range (tensorPauli (I := A))) := by
    change M ∈ pauliTensorSpan A
    rw [tensorPauli_span_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
  refine ⟨c, ?_⟩
  have hQ := congrArg (localEmbedLinearMap (n := n) (dim := fun _ => 2) A) hc
  change (localEmbedLinearMap (n := n) (dim := fun _ => 2) A)
    (∑ p, c p • tensorPauli p) = localEmbed A M at hQ
  rw [map_sum] at hQ
  simp_rw [map_smul] at hQ
  rw [hM]
  exact hQ.symm.trans (Finset.sum_congr rfl fun p _ => congrArg (c p • ·)
    (pauliMatrix_extendLocalPauli_eq_localEmbed A p).symm)

private theorem localProduct_mul_stabilizer_trace_zero
    (A : Finset (Fin n))
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hPauli : ∀ U ∈ S, IsPauli (U : Operator (QubitBasis n)))
    (hNoLocal : ∀ U ∈ S, SupportedOn (U : Operator (QubitBasis n)) A → U = 1)
    (p q : A → SinglePauli) (hpq : p ≠ q) (U : S) :
    ((onSupport A p * onSupport A q) * (U.val : Operator (QubitBasis n))).trace = 0 := by
  classical
  have hprod : SupportedOn (onSupport A p * onSupport A q) A :=
    (pauliMatrix_extendLocalPauli_supportedOn A p).mul_same
      (pauliMatrix_extendLocalPauli_supportedOn A q)
  obtain ⟨b, s, hs⟩ := isPauli_mul
    (show IsPauli (onSupport A p) from ⟨0, extendLocalPauli A p, rfl⟩)
    (show IsPauli (onSupport A q) from ⟨0, extendLocalPauli A q, rfl⟩)
  obtain ⟨a, r, hr⟩ := hPauli U.val U.property
  by_cases hrs : s = r
  · subst r
    have hscalar : (U.val : Operator (QubitBasis n)) =
        (Complex.I ^ a.val * (Complex.I ^ b.val)⁻¹) • (onSupport A p * onSupport A q) := by
      rw [hr, hs, pauliMatrix_eq_phase_smul a, pauliMatrix_eq_phase_smul b, smul_smul]
      rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), mul_one]
    have hU := hNoLocal U.val U.property (hscalar.symm ▸ hprod.smul _)
    rw [hU]
    change ((onSupport A p * onSupport A q) * (1 : Operator (QubitBasis n))).trace = _
    rw [Matrix.mul_one]
    exact pauli_mul_trace_eq_zero_of_ne (fun h => hpq (extendLocalPauli_injective A h))
  · rw [hs, hr, pauliMatrix_eq_phase_smul a, pauliMatrix_eq_phase_smul b,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul,
      pauli_mul_trace_eq_zero_of_ne hrs, smul_zero, smul_zero]

/-- Without a supported nonidentity stabilizer, distinct Pauli words
remain trace-orthogonal on the code, and each diagonal term is the
dimension of the encoded space. -/
theorem localPauli_restricted_trace (C : Code n (fun _ => 2) (2 ^ k) 1)
    (A : Finset (Fin n)) (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hPauli : ∀ U ∈ S, IsPauli (U : Operator (QubitBasis n)))
    (hSpace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (hNoLocal : ∀ U ∈ S, SupportedOn (U : Operator (QubitBasis n)) A → U = 1)
    (p q : A → SinglePauli) :
    (C.encoding.conjTranspose * onSupport A p * onSupport A q * C.encoding).trace =
      if p = q then (Fintype.card (Fin (2 ^ k) × Fin 1) : ℂ) else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    rw [ite_eq_left rfl]
    have hs : onSupport A p * onSupport A p = 1 := unphased_pauliMatrix_sq _
    calc
      _ = (C.encoding.conjTranspose * ((onSupport A p * onSupport A p) * C.encoding)).trace := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hs, Matrix.one_mul, C.isometry, Matrix.trace_one]
  · rw [ite_eq_right hpq]
    have hfinite : (S : Set (Matrix.unitaryGroup (QubitBasis n) ℂ)).Finite := by
      have h := (CriticalDepth.ReviewV2.pauliOperator_set_finite n).preimage
        (f := fun U : Matrix.unitaryGroup (QubitBasis n) ℂ => U.val) Subtype.val_injective.injOn
      exact h.subset hPauli
    let : Fintype S := hfinite.fintype
    let Q := onSupport A p * onSupport A q
    have htotal : (Q * (∑ U : S, (U.val : Operator (QubitBasis n)))).trace = 0 := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      exact Finset.sum_eq_zero fun U _ =>
        localProduct_mul_stabilizer_trace_zero A S hPauli hNoLocal p q hpq U
    have hrot :
        (C.encoding.conjTranspose * onSupport A p * onSupport A q * C.encoding).trace =
          (Q * (C.encoding * C.encoding.conjTranspose)).trace := by
      calc
        _ = (C.encoding.conjTranspose * (Q * C.encoding)).trace := by
          simp only [Q, Matrix.mul_assoc]
        _ = ((Q * C.encoding) * C.encoding.conjTranspose).trace :=
          Matrix.trace_mul_comm _ _
        _ = _ := by rw [Matrix.mul_assoc]
    rw [hrot]
    rw [subgroup_sum_eq_card_smul_projector C.encoding C.isometry S hSpace,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at htotal
    exact (mul_eq_zero.mp htotal).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

private theorem restricted_trace_eq_zero_of_anticommute
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (P O W : Operator (QubitBasis n)) (hW : IsUnitary W)
    (hFix : W * C.encoding = C.encoding)
    (hCode : W * (O * C.encoding) = O * C.encoding)
    (hAnti : W * P = -(P * W)) :
    (C.encoding.conjTranspose * P * O * C.encoding).trace = 0 := by
  have hLeft := encoding_adjoint_fixed_of_fixed C W hW hFix
  let M := C.encoding.conjTranspose * P * O * C.encoding
  have h : M = -M := by
    calc
      M = ((C.encoding.conjTranspose * W) * P) * (O * C.encoding) := by
        rw [hLeft]; exact Matrix.mul_assoc _ _ _
      _ = C.encoding.conjTranspose * ((W * P) * (O * C.encoding)) := by
        simp only [Matrix.mul_assoc]
      _ = -M := by
        rw [hAnti, Matrix.neg_mul, Matrix.mul_neg]
        simp only [M, Matrix.mul_assoc, hCode]
  have hz := congrArg Matrix.trace h
  rw [Matrix.trace_neg] at hz
  change M.trace = -M.trace at hz
  change M.trace = 0
  linear_combination (1 / 2 : ℂ) * hz

/-- The coefficients of a supported, code-preserving operator vanish
whenever a stabilizer anticommutes with the corresponding Pauli word. -/
theorem exists_localPauli_expansion_centralizer (C : Code n (fun _ => 2) (2 ^ k) 1)
    (A : Finset (Fin n)) (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hPauli : ∀ U ∈ S, IsPauli (U : Operator (QubitBasis n)))
    (hSpace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (hNoLocal : ∀ U ∈ S, SupportedOn (U : Operator (QubitBasis n)) A → U = 1)
    (O : Operator (QubitBasis n)) (hSupport : SupportedOn O A)
    (hPreserves : ∃ F : Operator (Fin (2 ^ k) × Fin 1), O * C.encoding = C.encoding * F) :
    ∃ c : (A → SinglePauli) → ℂ, O = ∑ p, c p • pauliMatrix 0 (extendLocalPauli A p) ∧
      ∀ p, c p ≠ 0 → ∀ U ∈ S, (U : Operator (QubitBasis n)) * pauliMatrix 0 (extendLocalPauli A p) =
        pauliMatrix 0 (extendLocalPauli A p) * (U : Operator (QubitBasis n)) := by
  classical
  obtain ⟨c, hc⟩ := exists_supported_pauli_expansion A O hSupport
  refine ⟨c, hc, ?_⟩
  intro p hp U hU
  obtain ⟨a, r, hr⟩ := hPauli U hU
  have hd := pauliMatrix_commute_or_anticommute a 0 r (extendLocalPauli A p)
  rw [← hr] at hd
  rcases hd with hcomm | hanti
  · exact hcomm
  · exfalso
    have hfix := encoding_fixed_of_fixedSpace C S hSpace U hU
    obtain ⟨F, hF⟩ := hPreserves
    have hcode : (U : Operator (QubitBasis n)) * (O * C.encoding) = O * C.encoding := by
      rw [hF, ← Matrix.mul_assoc, hfix]
    have hz := restricted_trace_eq_zero_of_anticommute C (onSupport A p) O U
      ⟨U.property.1, U.property.2⟩ hfix hcode hanti
    change O = ∑ q, c q • onSupport A q at hc
    rw [hc, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum] at hz
    simp_rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      localPauli_restricted_trace C A S hPauli hSpace hNoLocal] at hz
    rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p)] at hz
    · rw [ite_eq_left rfl, smul_eq_mul] at hz
      have hdim : (Fintype.card (Fin (2 ^ k) × Fin 1) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (by
          simpa only [Fintype.card_prod, Fintype.card_fin, mul_one] using
            (show 0 < 2 ^ k from by positivity)))
      exact hp ((mul_eq_zero.mp hz).resolve_right hdim)
    · intro q _ hqp
      rw [ite_eq_right (Ne.symm hqp), smul_zero]

#print axioms localPauli_restricted_trace
#print axioms exists_localPauli_expansion_centralizer

end CriticalDepth.Manuscript20261114.CSSPauliRestriction
