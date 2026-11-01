import CriticalDepth.PauliSpan
import CriticalDepth.Support

/-!
# A minimum-weight logical Pauli from the original stabilizer-code hypotheses

The Pauli witness is derived from an arbitrary undetectable supported operator
using the concrete Pauli span. It is not an additional premise. The stabilizer
fixed-space equality is then used to obtain actual code preservation.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker BigOperators

variable {n K g d : ℕ} {dim : Fin n → ℕ}

def gaugeOnlyComplexSubmodule (C : Code n dim K g) :
    Submodule ℂ (Operator (PhysicalBasis n dim)) where
  carrier := {O | GaugeOnly C O}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    rintro A B ⟨MA, hA⟩ ⟨MB, hB⟩
    refine ⟨MA + MB, ?_⟩
    rw [Matrix.mul_add, Matrix.add_mul, hA, hB, Matrix.kronecker_add]
  smul_mem' := by
    rintro z A ⟨M, hM⟩
    refine ⟨z • M, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, hM, Matrix.kronecker_smul]

def pauliSupport (p : Fin n → SinglePauli) : Finset (Fin n) :=
  Finset.univ.filter fun i => p i ≠ .I

theorem pauliSupport_subset_of_outside_identity
    (S : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ S → p i = .I) : pauliSupport p ⊆ S := by
  intro i hi
  by_contra hiS
  exact (Finset.mem_filter.mp hi).2 (hout i hiS)

theorem pauliMatrix_supportedOn_pauliSupport (p : Fin n → SinglePauli) :
    SupportedOn (pauliMatrix (0 : Fin 4) p) (pauliSupport p) := by
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  by_contra hp
  exact hi (by simp [pauliSupport, hp])

theorem actualDistance_exists_nongauge_unphasedPauli
    (C : Code n (fun _ => 2) K g) (hdistance : HasActualDistance C d) :
    ∃ p : Fin n → SinglePauli, (pauliSupport p).card = d ∧
      ¬ GaugeOnly C (pauliMatrix (0 : Fin 4) p) := by
  classical
  obtain ⟨hdetect, S, hS, O, hOsupported, hOnongauge⟩ := hdistance
  obtain ⟨A, hAencoding⟩ := hOsupported
  have hex : ∃ p : S → SinglePauli,
      ¬ GaugeOnly C (pauliMatrix (0 : Fin 4) (extendLocalPauli S p)) := by
    by_contra hn
    have hall : ∀ p : S → SinglePauli,
        GaugeOnly C (pauliMatrix (0 : Fin 4) (extendLocalPauli S p)) := by
      intro p
      by_contra hp
      exact hn ⟨p, hp⟩
    let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin n => 2) S)) :=
      (gaugeOnlyComplexSubmodule C).comap (localEmbedLinearMap S)
    have hspan : pauliTensorSpan S ≤ B := by
      apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      change GaugeOnly C (localEmbed S (tensorPauli p))
      rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
      exact hall p
    rw [tensorPauli_span_eq_top] at hspan
    have hA : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
    change GaugeOnly C (localEmbed S A) at hA
    apply hOnongauge
    simpa only [hAencoding] using hA
  obtain ⟨p, hp⟩ := hex
  let pfull : Fin n → SinglePauli := extendLocalPauli S p
  have hout : ∀ i, i ∉ S → pfull i = .I := by
    intro i hi
    simp [pfull, extendLocalPauli, hi]
  have hsubset : pauliSupport pfull ⊆ S :=
    pauliSupport_subset_of_outside_identity S pfull hout
  have hle : (pauliSupport pfull).card ≤ d := by
    simpa only [hS] using Finset.card_le_card hsubset
  have hge : d ≤ (pauliSupport pfull).card := by
    by_contra hn
    have hlt : (pauliSupport pfull).card < d := by omega
    apply hp
    exact hdetect (pauliSupport pfull) hlt (pauliMatrix (0 : Fin 4) pfull)
      (pauliMatrix_supportedOn_pauliSupport pfull)
  exact ⟨pfull, Nat.le_antisymm hle hge, hp⟩

/-- Every encoding column belongs to the encoded range, with an explicit coordinate vector. -/
theorem encoding_column_mem_range (C : Code n dim K g) (j : Fin K × Fin g) :
    (fun x => C.encoding x j) ∈ Set.range (fun v => C.encoding.mulVec v) := by
  classical
  refine ⟨fun i => if i = j then 1 else 0, ?_⟩
  funext x
  simp [Matrix.mulVec, dotProduct, mul_ite]

theorem encoding_fixed_of_fixedSpace
    (C : Code n dim K g)
    (S : Subgroup (Matrix.unitaryGroup (PhysicalBasis n dim) ℂ))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)).mulVec v = v})
    (U : Matrix.unitaryGroup (PhysicalBasis n dim) ℂ) (hUS : U ∈ S) :
    (U : Operator (PhysicalBasis n dim)) * C.encoding = C.encoding := by
  ext x j
  have hcol := encoding_column_mem_range C j
  rw [hspace] at hcol
  have hh := congrFun (hcol U hUS) x
  change ((U : Operator (PhysicalBasis n dim)) * C.encoding) x j = C.encoding x j at hh
  exact hh

theorem encoding_adjoint_fixed_of_fixed
    (C : Code n dim K g) (U : Operator (PhysicalBasis n dim))
    (hU : IsUnitary U) (hfix : U * C.encoding = C.encoding) :
    C.encoding.conjTranspose * U = C.encoding.conjTranspose := by
  have hh := congrArg Matrix.conjTranspose hfix
  have hstar : C.encoding.conjTranspose * U.conjTranspose = C.encoding.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul] using hh
  have hUleft : U.conjTranspose * U = 1 := hU.1
  calc
    C.encoding.conjTranspose * U = (C.encoding.conjTranspose * U.conjTranspose) * U := by
      rw [hstar]
    _ = C.encoding.conjTranspose := by rw [Matrix.mul_assoc, hUleft, Matrix.mul_one]

theorem gaugeOnly_of_compression_zero
    (C : Code n dim K g) (P : Operator (PhysicalBasis n dim))
    (hzero : C.encoding.conjTranspose * P * C.encoding = 0) : GaugeOnly C P := by
  refine ⟨0, ?_⟩
  rw [hzero]
  simp

theorem anticommuting_fixed_operator_gaugeOnly
    (C : Code n dim K g) (P U : Operator (PhysicalBasis n dim))
    (hU : IsUnitary U) (hfix : U * C.encoding = C.encoding)
    (hanti : U * P = -(P * U)) : GaugeOnly C P := by
  have hEfix := encoding_adjoint_fixed_of_fixed C U hU hfix
  have hneg : C.encoding.conjTranspose * P * C.encoding =
      -(C.encoding.conjTranspose * P * C.encoding) := by
    calc
      C.encoding.conjTranspose * P * C.encoding =
          (C.encoding.conjTranspose * U) * P * C.encoding := by rw [hEfix]
      _ = C.encoding.conjTranspose * (U * P) * C.encoding := by
        simp only [Matrix.mul_assoc]
      _ = -(C.encoding.conjTranspose * (P * U) * C.encoding) := by
        rw [hanti]
        simp only [Matrix.mul_neg, Matrix.neg_mul]
      _ = -(C.encoding.conjTranspose * P * C.encoding) := by
        simp only [Matrix.mul_assoc, hfix]
  apply gaugeOnly_of_compression_zero C P
  ext i j
  change (C.encoding.conjTranspose * P * C.encoding) i j = 0
  have hh := congrArg (fun A : Operator (Fin K × Fin g) => A i j) hneg
  change (C.encoding.conjTranspose * P * C.encoding) i j =
    -((C.encoding.conjTranspose * P * C.encoding) i j) at hh
  linear_combination (1 / 2 : ℂ) * hh

theorem pauli_commutes_stabilizer_of_nongauge
    {k : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hpauli : ∀ U ∈ S, IsPauli (U : Operator (QubitBasis n)))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (p : Fin n → SinglePauli) (hnongauge : ¬ GaugeOnly C (pauliMatrix (0 : Fin 4) p)) :
    ∀ U ∈ S, (U : Operator (QubitBasis n)) * pauliMatrix (0 : Fin 4) p =
      pauliMatrix (0 : Fin 4) p * (U : Operator (QubitBasis n)) := by
  intro U hUS
  obtain ⟨a, q, hU⟩ := hpauli U hUS
  have hcases := pauliMatrix_commute_or_anticommute a (0 : Fin 4) q p
  rw [← hU] at hcases
  rcases hcases with hcomm | hanti
  · exact hcomm
  · exact False.elim (hnongauge (anticommuting_fixed_operator_gaugeOnly C
      (pauliMatrix (0 : Fin 4) p) (U : Operator (QubitBasis n))
      ⟨U.2.1, U.2.2⟩ (encoding_fixed_of_fixedSpace C S hspace U hUS) hanti))

theorem code_preservation_of_stabilizer_commutation
    (C : Code n dim K g)
    (S : Subgroup (Matrix.unitaryGroup (PhysicalBasis n dim) ℂ))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)).mulVec v = v})
    (P : Operator (PhysicalBasis n dim))
    (hcomm : ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)) * P =
      P * (U : Operator (PhysicalBasis n dim))) :
    P * C.encoding = C.encoding * (C.encoding.conjTranspose * P * C.encoding) := by
  classical
  have hcolrange : ∀ j : Fin K × Fin g,
      ∃ v : (Fin K × Fin g) → ℂ, C.encoding.mulVec v = fun x => (P * C.encoding) x j := by
    intro j
    have hfixed : (fun x => (P * C.encoding) x j) ∈
        {v | ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)).mulVec v = v} := by
      intro U hUS
      have hfix := encoding_fixed_of_fixedSpace C S hspace U hUS
      have hm : (U : Operator (PhysicalBasis n dim)) * (P * C.encoding) = P * C.encoding := by
        calc
          (U : Operator (PhysicalBasis n dim)) * (P * C.encoding) =
              ((U : Operator (PhysicalBasis n dim)) * P) * C.encoding := by rw [Matrix.mul_assoc]
          _ = (P * (U : Operator (PhysicalBasis n dim))) * C.encoding := by rw [hcomm U hUS]
          _ = P * C.encoding := by rw [Matrix.mul_assoc, hfix]
      funext x
      change ((U : Operator (PhysicalBasis n dim)) * (P * C.encoding)) x j =
        (P * C.encoding) x j
      rw [hm]
    rw [← hspace] at hfixed
    exact hfixed
  let Y : Operator (Fin K × Fin g) := fun i j => Classical.choose (hcolrange j) i
  have hPY : P * C.encoding = C.encoding * Y := by
    ext x j
    have hh := congrFun (Classical.choose_spec (hcolrange j)) x
    change (C.encoding * Y) x j = (P * C.encoding) x j at hh
    exact hh.symm
  have hY : Y = C.encoding.conjTranspose * P * C.encoding := by
    calc
      Y = (C.encoding.conjTranspose * C.encoding) * Y := by rw [C.isometry]; simp
      _ = C.encoding.conjTranspose * (C.encoding * Y) := by rw [Matrix.mul_assoc]
      _ = C.encoding.conjTranspose * (P * C.encoding) := by rw [← hPY]
      _ = C.encoding.conjTranspose * P * C.encoding := by rw [Matrix.mul_assoc]
  rw [hPY, hY]

def subspaceLogicalMatrix (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim)) :
    Operator (Fin K) :=
  fun i j => (C.encoding.conjTranspose * P * C.encoding) (i, 0) (j, 0)

theorem subspaceCompression_eq_kronecker
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim)) :
    C.encoding.conjTranspose * P * C.encoding =
      subspaceLogicalMatrix C P ⊗ₖ (1 : Operator (Fin 1)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a
  subst b
  simp [subspaceLogicalMatrix, Matrix.kronecker_apply]

theorem codeCompression_selfAdjoint
    (C : Code n dim K g) (P : Operator (PhysicalBasis n dim))
    (hself : P.conjTranspose = P) :
    (C.encoding.conjTranspose * P * C.encoding).conjTranspose =
      C.encoding.conjTranspose * P * C.encoding := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hself, Matrix.mul_assoc]

theorem codeCompression_sq_of_preserving
    (C : Code n dim K g) (P : Operator (PhysicalBasis n dim))
    (hsq : P * P = 1)
    (hpreserve : P * C.encoding =
      C.encoding * (C.encoding.conjTranspose * P * C.encoding)) :
    (C.encoding.conjTranspose * P * C.encoding) *
      (C.encoding.conjTranspose * P * C.encoding) = 1 := by
  let Q : Operator (Fin K × Fin g) := C.encoding.conjTranspose * P * C.encoding
  have hp : P * C.encoding = C.encoding * Q := hpreserve
  change Q * Q = 1
  calc
    Q * Q = (C.encoding.conjTranspose * P) * (C.encoding * Q) := by
      dsimp [Q]
      simp only [Matrix.mul_assoc]
    _ = (C.encoding.conjTranspose * P) * (P * C.encoding) := by rw [← hp]
    _ = C.encoding.conjTranspose * (P * P) * C.encoding := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hsq, Matrix.mul_one, C.isometry]

theorem subspaceLogicalMatrix_selfAdjoint
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hself : P.conjTranspose = P) :
    (subspaceLogicalMatrix C P).conjTranspose = subspaceLogicalMatrix C P := by
  ext i j
  have hh := congrArg (fun A : Operator (Fin K × Fin 1) => A (i, 0) (j, 0))
    (codeCompression_selfAdjoint C P hself)
  simpa only [subspaceLogicalMatrix, Matrix.conjTranspose_apply] using hh

theorem subspaceLogicalMatrix_sq_of_preserving
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hsq : P * P = 1)
    (hpreserve : P * C.encoding =
      C.encoding * (C.encoding.conjTranspose * P * C.encoding)) :
    subspaceLogicalMatrix C P * subspaceLogicalMatrix C P = 1 := by
  have hc := codeCompression_sq_of_preserving C P hsq hpreserve
  simp only [subspaceCompression_eq_kronecker C P] at hc
  rw [← Matrix.mul_kronecker_mul (subspaceLogicalMatrix C P) (subspaceLogicalMatrix C P)
    (1 : Operator (Fin 1)) (1 : Operator (Fin 1))] at hc
  simp only [one_mul] at hc
  ext i j
  have hh := congrArg (fun A : Operator (Fin K × Fin 1) => A (i, 0) (j, 0)) hc
  simpa [Matrix.kronecker_apply, Matrix.one_apply] using hh

theorem subspaceLogicalMatrix_nonscalar_of_nongauge
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hnongauge : ¬ GaugeOnly C P) : ¬ IsScalar (subspaceLogicalMatrix C P) := by
  rintro ⟨z, hz⟩
  apply hnongauge
  refine ⟨z • (1 : Operator (Fin 1)), ?_⟩
  calc
    C.encoding.conjTranspose * P * C.encoding =
        subspaceLogicalMatrix C P ⊗ₖ (1 : Operator (Fin 1)) :=
      subspaceCompression_eq_kronecker C P
    _ = (z • (1 : Operator (Fin K))) ⊗ₖ (1 : Operator (Fin 1)) := by rw [hz]
    _ = (1 : Operator (Fin K)) ⊗ₖ (z • (1 : Operator (Fin 1))) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      change (z * (1 : Operator (Fin K)) i j) * (1 : Operator (Fin 1)) a b =
        (1 : Operator (Fin K)) i j * (z * (1 : Operator (Fin 1)) a b)
      ring

theorem subspaceLogicalMatrix_implements_of_preserving
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hunitary : IsUnitary (subspaceLogicalMatrix C P))
    (hpreserve : P * C.encoding =
      C.encoding * (C.encoding.conjTranspose * P * C.encoding)) :
    Implements C P (subspaceLogicalMatrix C P) := by
  refine ⟨hunitary, 1, ?_, ?_⟩
  · constructor <;> simp
  · exact hpreserve.trans
      (congrArg (fun A : Operator (Fin K × Fin 1) => C.encoding * A)
        (subspaceCompression_eq_kronecker C P))

/--
The minimum-weight nonscalar logical Pauli follows from the original actual
distance and stabilizer fixed-space hypotheses. No Pauli witness, preservation
predicate, or desired logical action is supplied as an extra hypothesis.
-/
theorem stabilizer_actualDistance_logicalPauli
    {k : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    ∃ (p : Fin n → SinglePauli) (W : Operator (Fin (2 ^ k))),
      (pauliSupport p).card = d ∧
      Implements C (pauliMatrix (0 : Fin 4) p) W ∧
      IsUnitary W ∧ W.conjTranspose = W ∧ W * W = 1 ∧ ¬ IsScalar W := by
  classical
  obtain ⟨p, hcard, hnongauge⟩ := actualDistance_exists_nongauge_unphasedPauli C hdistance
  obtain ⟨S, hpauli, hspace⟩ := hstabilizer
  let P : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) p
  have hcomm := pauli_commutes_stabilizer_of_nongauge C S hpauli hspace p hnongauge
  have hpreserve := code_preservation_of_stabilizer_commutation C S hspace P hcomm
  have hself : (subspaceLogicalMatrix C P).conjTranspose = subspaceLogicalMatrix C P :=
    subspaceLogicalMatrix_selfAdjoint C P (unphased_pauliMatrix_selfAdjoint p)
  have hsq : subspaceLogicalMatrix C P * subspaceLogicalMatrix C P = 1 :=
    subspaceLogicalMatrix_sq_of_preserving C P (unphased_pauliMatrix_sq p) hpreserve
  have hunitary : IsUnitary (subspaceLogicalMatrix C P) := by
    constructor
    · change (subspaceLogicalMatrix C P).conjTranspose * subspaceLogicalMatrix C P = 1
      rw [hself, hsq]
    · change subspaceLogicalMatrix C P * (subspaceLogicalMatrix C P).conjTranspose = 1
      rw [hself, hsq]
  have hnonscalar := subspaceLogicalMatrix_nonscalar_of_nongauge C P hnongauge
  exact ⟨p, subspaceLogicalMatrix C P, hcard,
    subspaceLogicalMatrix_implements_of_preserving C P hunitary hpreserve,
    hunitary, hself, hsq, hnonscalar⟩

end CriticalDepth.Manuscript
