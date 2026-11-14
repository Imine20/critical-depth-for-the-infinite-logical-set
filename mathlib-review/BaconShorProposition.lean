import BaconShorAspectRatio
import BaconShorAdjacentGauges
import BaconShorFixedSpace
import BaconShorRealLog
import ExactGeneration

/-!
# The rectangular Bacon--Shor proposition and its two aspect-ratio consequences
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 CriticalDepth.Arithmetic
open scoped ENat Kronecker

noncomputable section

variable {m b : ℕ}

/-- Weights of physical Pauli operators inducing a nonscalar bare
action on the protected qubit. -/
def baconBareLogicalWeights (m b : ℕ) : Set ℕ :=
  {w | ∃ (phase : Fin 4) (p : Fin ((m+1)*(b+1)) → SinglePauli) (A : Operator (Fin 2)),
    (pauliSupport p).card = w ∧ ¬ IsScalar A ∧
      pauliMatrix phase p * (baconShorCode m b).encoding =
        (baconShorCode m b).encoding * (A ⊗ₖ (1 : Operator (Fin (2 ^ (m*b)))))}

theorem baconShor_bareDistance (hmb : m ≤ b) :
    IsLeast (baconBareLogicalWeights m b) (m + 1) := by
  classical
  constructor
  · refine ⟨0, physicalXWord (fullXColumn (rows := m+1) (0 : Fin (b+1))),
      SinglePauli.X.matrix, fullXColumn_support_card 0, ?_, baconPhysicalEncoding_bareX⟩
    rintro ⟨z, hz⟩
    have h := congrArg (fun M : Operator (Fin 2) => M 0 1) hz
    norm_num [SinglePauli.matrix, Matrix.one_apply, Matrix.smul_apply] at h
  · rintro _ ⟨phase, p, A, rfl, hnonscalar, henc⟩
    by_contra! hsmall
    let C := baconShorCode m b
    have hsupport : SupportedOn (pauliMatrix phase p) (pauliSupport p) := by
      have hp := (pauliMatrix_supportedOn_pauliSupport p).smul (Complex.I ^ phase.val)
      have heq : pauliMatrix phase p = (Complex.I ^ phase.val) • pauliMatrix 0 p := by
        ext x y
        simp [pauliMatrix, Matrix.smul_apply, smul_eq_mul]
      exact heq ▸ hp
    obtain ⟨G, hG⟩ := (baconShorCode_hasActualDistance hmb).1
      (pauliSupport p) hsmall (pauliMatrix phase p) hsupport
    have hcompress : C.encoding.conjTranspose * pauliMatrix phase p * C.encoding =
        A ⊗ₖ (1 : Operator (Fin (2 ^ (m*b)))) := by
      rw [Matrix.mul_assoc, henc, ← Matrix.mul_assoc, C.isometry, Matrix.one_mul]
    rw [hcompress] at hG
    let a : Fin (2 ^ (m*b)) := ⟨0, by positivity⟩
    apply hnonscalar
    refine ⟨G a a, ?_⟩
    ext i j
    have e := congrArg (fun M : Operator (Fin 2 × Fin (2 ^ (m*b))) => M (i,a) (j,a)) hG
    simpa only [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one, Matrix.smul_apply,
      smul_eq_mul, mul_comm] using e

theorem projectiveXAxisNormalizer_isClosed :
    IsClosed (projectiveXAxisNormalizer : Set (PU (Fin 2))) := by
  let f : Matrix.unitaryGroup (Fin 2) ℂ → Operator (Fin 2) :=
    fun U => U.val * SinglePauli.X.matrix * star U.val
  have hf : Continuous f := by
    have hu : Continuous (fun U : Matrix.unitaryGroup (Fin 2) ℂ => U.val) :=
      continuous_subtype_val
    exact (hu.mul continuous_const).mul (continuous_star.comp hu)
  have hpre :
      (projectiveMk (Fin 2) : Matrix.unitaryGroup (Fin 2) ℂ → PU (Fin 2)) ⁻¹'
          (projectiveXAxisNormalizer : Set (PU (Fin 2))) =
        {U | f U = SinglePauli.X.matrix} ∪ {U | f U = -SinglePauli.X.matrix} := by
    ext U
    change projectiveMk (Fin 2) U ∈ projectiveXAxisNormalizer ↔ preservesXAxis U
    constructor
    · rintro ⟨V, hV, hUV⟩
      exact preservesXAxis_of_projectivelyEquivalent U V ((projectiveMk_eq_iff _ _ _).mp hUV.symm) hV
    · intro hU
      exact ⟨U, hU, rfl⟩
  apply (QuotientGroup.isQuotientMap_mk (scalarPhaseSubgroup (Fin 2))).isClosed_preimage.mp
  change IsClosed ((projectiveMk (Fin 2) : Matrix.unitaryGroup (Fin 2) ℂ → PU (Fin 2)) ⁻¹'
    (projectiveXAxisNormalizer : Set (PU (Fin 2))))
  rw [hpre]
  exact (isClosed_eq hf continuous_const).union (isClosed_eq hf continuous_const)

theorem baconShor_nativeDenseDepth_above (q h : ℕ) (hq : 2 ≤ q) (hsize : (m+1)*q^h < b+1) :
    (h : ℕ∞) < nativeDenseDepth (baconShorCode m b).encoding q := by
  apply lt_of_not_ge
  intro hd
  have hDense := ((nativeDenseDepth_le_nat_iff (baconShorCode m b).encoding q h).mp hd).2
  exact not_dense_subgroupClosure_of_subset_closed (baconNativeLogicalImage_axis (by omega) hsize)
    projectiveXAxisNormalizer_isClosed projectiveXAxisNormalizer_ne_top hDense

/-- The +1 space of the physical center of the adjacent-pair gauge masks. -/
def baconAdjacentCenterFixedSpace (m b : ℕ) : Set (QubitBasis ((m+1)*(b+1)) → ℂ) :=
  {v | (∀ x : BaconMask m b,
      x ∈ Submodule.span Bit (Set.range (fun p : Fin (m+1) × Fin b => horizontalPair p.1 p.2)) →
      (∀ z ∈ Submodule.span Bit (Set.range (fun p : Fin m × Fin (b+1) => verticalPair p.1 p.2)),
        maskDot x z = 0) → (pauliMatrix 0 (physicalXWord x)).mulVec v = v) ∧
    (∀ z : BaconMask m b,
      z ∈ Submodule.span Bit (Set.range (fun p : Fin m × Fin (b+1) => verticalPair p.1 p.2)) →
      (∀ x ∈ Submodule.span Bit (Set.range (fun p : Fin (m+1) × Fin b => horizontalPair p.1 p.2)),
        maskDot z x = 0) → (pauliMatrix 0 (physicalZWord z)).mulVec v = v)}

theorem baconShorCode_range_eq_adjacentCenter :
    Set.range (fun w => (baconShorCode m b).encoding.mulVec w) = baconAdjacentCenterFixedSpace m b := by
  change Set.range (fun w => (baconPhysicalEncoding m b).mulVec w) = baconAdjacentCenterFixedSpace m b
  rw [baconPhysicalEncoding_range_eq_center]
  ext v
  constructor
  · rintro ⟨hX,hZ⟩
    exact ⟨fun x hx hz => hX x ((centerX_iff_adjacentGaugeCenter x).mpr ⟨hx,hz⟩),
      fun z hz hx => hZ z ((centerZ_iff_adjacentGaugeCenter z).mpr ⟨hz,hx⟩)⟩
  · rintro ⟨hX,hZ⟩
    exact ⟨fun x hx => hX x ((centerX_iff_adjacentGaugeCenter x).mp hx).1
        ((centerX_iff_adjacentGaugeCenter x).mp hx).2,
      fun z hz => hZ z ((centerZ_iff_adjacentGaugeCenter z).mp hz).1
        ((centerZ_iff_adjacentGaugeCenter z).mp hz).2⟩


theorem baconShor_proposition (hm : 1 ≤ m) (hmb : m ≤ b) (q : ℕ) (hq : 2 ≤ q) :
    Set.range (fun w => (baconShorCode m b).encoding.mulVec w) = baconAdjacentCenterFixedSpace m b ∧
      HasActualDistance (baconShorCode m b) (m + 1) ∧
      IsLeast (baconBareLogicalWeights m b) (m + 1) ∧
      nativeCriticalDepth (baconShorCode m b).encoding q = (criticalDepth q (m+1) : ℕ∞) ∧
      max (nativeCriticalDepth (baconShorCode m b).encoding q)
        ((⌈Real.logb (q : ℝ) (((b+1 : ℕ) : ℝ) / ((m+1 : ℕ) : ℝ))⌉₊ : ℕ) : ℕ∞) ≤ nativeExactDepth (baconShorCode m b).encoding q ∧
      nativeExactDepth (baconShorCode m b).encoding q ≤ (criticalDepth q (b+1) : ℕ∞) := by
  refine ⟨baconShorCode_range_eq_adjacentCenter, baconShorCode_hasActualDistance hmb,
    baconShor_bareDistance hmb,
    baconShor_nativeCriticalDepth hm hmb q hq, ?_, baconShor_nativeExactDepth_upper hm hmb q hq⟩
  exact max_le ((le_max_left _ _).trans
      (max_nativeCriticalDepth_nativeDenseDepth_le_nativeExactDepth (baconShorCode m b).encoding q (by decide)))
    (by
      rw [natCeil_log_ratio_eq_clog_ceilDiv q (m+1) (b+1) hq (by omega) (by omega)]
      exact baconShor_exactDepth_ratio_lower hq)

theorem baconShor_elongated_thresholds (hm : 1 ≤ m) (hmb : m ≤ b) (q : ℕ) (hq : 2 ≤ q)
    (hsize : (m+1)*q^(criticalDepth q (m+1)) < b+1) :
    nativeCriticalDepth (baconShorCode m b).encoding q <
        nativeDenseDepth (baconShorCode m b).encoding q ∧
      nativeDenseDepth (baconShorCode m b).encoding q =
        nativeExactDepth (baconShorCode m b).encoding q := by
  let C := baconShorCode m b
  have hlt : nativeCriticalDepth C.encoding q < nativeDenseDepth C.encoding q := by
    rw [baconShor_nativeCriticalDepth hm hmb q hq]
    exact baconShor_nativeDenseDepth_above q (criticalDepth q (m+1)) hq hsize
  refine ⟨hlt, ?_⟩
  have hg : 1 ≤ 2 ^ (m*b) := Nat.succ_le_of_lt (by positivity : 0 < 2 ^ (m*b))
  rw [nativeExactDepth_eq_max C.encoding C.isometry (by decide) hg, max_eq_right hlt.le]

theorem baconShor_nonsquare_shell_family (q j : ℕ) (hq : 2 ≤ q) (hj : 1 ≤ j) :
    q^j + 1 < q^(j+1) ∧
      nativeCriticalDepth (baconShorCode (q^j) (q^(j+1)-1)).encoding q = ((2*j+1 : ℕ) : ℕ∞) ∧
      nativeExactDepth (baconShorCode (q^j) (q^(j+1)-1)).encoding q = ((2*j+1 : ℕ) : ℕ∞) := by
  have hpow : 1 < q^j := one_lt_pow₀ (by omega : 1 < q) (by omega)
  have hnonsquare : q^j + 1 < q^(j+1) := by
    calc
      q^j + 1 < q^j + q^j := Nat.add_lt_add_left hpow _
      _ = q^j * 2 := (mul_two _).symm
      _ ≤ q^(j+1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hq
  have hmb : q^j ≤ q^(j+1)-1 := by omega
  have hclog : Nat.clog q (q^j+1) = j+1 := by
    apply le_antisymm
    · exact (Nat.clog_le_iff_le_pow (by omega)).mpr hnonsquare.le
    · by_contra! hsmall
      have hbad := (Nat.clog_le_iff_le_pow (by omega : 1 < q)).mp
        (show Nat.clog q (q^j+1) ≤ j by omega)
      omega
  have hshell : (q^(j+1)-1)+1 ≤ q ^ Nat.clog q (q^j+1) := by rw [hclog]; omega
  have hcalc : criticalDepth q (q^j+1) = 2*j+1 := by
    unfold criticalDepth
    rw [hclog]
    omega
  have hc := baconShor_nativeCriticalDepth (by omega : 1 ≤ q^j) hmb q hq
  rw [hcalc] at hc
  exact ⟨hnonsquare, hc, (baconShor_equal_thresholds_of_shell (by omega) hmb q hq hshell).trans hc⟩

#print axioms baconShor_bareDistance
#print axioms projectiveXAxisNormalizer_isClosed
#print axioms baconShorCode_range_eq_adjacentCenter
#print axioms baconShor_proposition
#print axioms baconShor_elongated_thresholds
#print axioms baconShor_nonsquare_shell_family

end

end CriticalDepth.FaultShorSaturation.BaconShor
