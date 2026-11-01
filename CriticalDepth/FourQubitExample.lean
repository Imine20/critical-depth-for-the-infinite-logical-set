import CriticalDepth.StabilizerWitness
import CriticalDepth.LayerOperations

/-!
# The concrete four-qubit distance-two subspace

The four columns are the normalized complementary pairs
0000/1111, 0011/1100, 0101/1010, and 0110/1001. All matrix entries
are explicit. Finite index calculations use kernel-reduced `decide` and
ordinary arithmetic tactics, never an external decision oracle.
-/

noncomputable section

namespace CriticalDepth.Manuscript.FourQubit

open Matrix
open scoped BigOperators Kronecker

def word : Fin 4 → QubitBasis 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 1, 0]]

def complement (x : QubitBasis 4) : QubitBasis 4 := fun i => 1 - x i

@[simp] theorem word_eq_word (i j : Fin 4) : word i = word j ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem complement_word_eq_complement_word (i j : Fin 4) :
    complement (word i) = complement (word j) ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem word_ne_complement_word (i j : Fin 4) :
    word i ≠ complement (word j) := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem complement_word_ne_word (i j : Fin 4) :
    complement (word i) ≠ word j := by
  fin_cases i <;> fin_cases j <;> decide

def dirac {α : Type*} [DecidableEq α] (a : α) (x : α) : ℂ := if x = a then 1 else 0

@[simp] theorem star_dirac {α : Type*} [DecidableEq α] (a x : α) :
    star (dirac a x) = dirac a x := by
  by_cases h : x = a <;> simp [dirac, h]

@[simp] theorem sum_dirac_mul {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℂ) : (∑ x, dirac a x * f x) = f a := by
  simp [dirac, ite_mul]

@[simp] theorem sum_mul_dirac {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℂ) : (∑ x, f x * dirac a x) = f a := by
  simp [dirac, mul_ite]

def scale : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)

theorem scale_norm : star scale * scale = (1 / 2 : ℂ) := by
  have hs : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = (1 / 2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  change star (Real.sqrt (1 / 2 : ℝ) : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) = _
  have hstar : star (Real.sqrt (1 / 2 : ℝ) : ℂ) = (Real.sqrt (1 / 2 : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [hstar]
  have hreal : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
    simpa only [pow_two] using hs
  simpa using congrArg Complex.ofReal hreal

def encoding : Matrix (QubitBasis 4) (Fin 4 × Fin 1) ℂ :=
  fun x j => scale * (dirac (word j.1) x + dirac (complement (word j.1)) x)

theorem encoding_adjoint_mul_entry (O : Operator (QubitBasis 4))
    (j : Fin 4 × Fin 1) (y : QubitBasis 4) :
    (encoding.conjTranspose * O) j y =
      star scale * (O (word j.1) y + O (complement (word j.1)) y) := by
  classical
  change (∑ x, star (scale * (dirac (word j.1) x +
    dirac (complement (word j.1)) x)) * O x y) = _
  calc
    _ = star scale * (∑ x, dirac (word j.1) x * O x y) +
        star scale * (∑ x, dirac (complement (word j.1)) x * O x y) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [star_mul, star_add, star_dirac, star_dirac]
      ring
    _ = _ := by rw [sum_dirac_mul, sum_dirac_mul, mul_add]

theorem encoding_compression_entry (O : Operator (QubitBasis 4))
    (j k : Fin 4 × Fin 1) :
    (encoding.conjTranspose * O * encoding) j k =
      (star scale * scale) *
        (O (word j.1) (word k.1) + O (word j.1) (complement (word k.1)) +
          O (complement (word j.1)) (word k.1) +
          O (complement (word j.1)) (complement (word k.1))) := by
  classical
  change (∑ x, (encoding.conjTranspose * O) j x * encoding x k) = _
  simp only [encoding_adjoint_mul_entry, encoding]
  calc
    _ = (star scale * scale) *
        ((∑ x, O (word j.1) x * dirac (word k.1) x) +
          (∑ x, O (word j.1) x * dirac (complement (word k.1)) x) +
          (∑ x, O (complement (word j.1)) x * dirac (word k.1) x) +
          (∑ x, O (complement (word j.1)) x * dirac (complement (word k.1)) x)) := by
      conv_rhs => simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by simp only [sum_mul_dirac]

theorem encoding_isometry : encoding.conjTranspose * encoding = 1 := by
  have hc := encoding_compression_entry (1 : Operator (QubitBasis 4))
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a
  fin_cases b
  change (encoding.conjTranspose * encoding) (i, 0) (j, 0) =
    (1 : Operator (Fin 4 × Fin 1)) (i, 0) (j, 0)
  have hh := hc (i, 0) (j, 0)
  simp only [Matrix.mul_one] at hh
  rw [hh, scale_norm]
  by_cases hij : i = j
  · subst j
    norm_num [Matrix.one_apply]
  · simp [Matrix.one_apply, hij]

def code : Code 4 (fun _ => 2) (2 ^ 2) 1 where
  encoding := encoding
  isometry := encoding_isometry

def sitePauli (site : Fin 4) (p : SinglePauli) : Fin 4 → SinglePauli :=
  fun i => if i = site then p else .I

def weightTwoPauli : Fin 4 → SinglePauli := fun i => if i = 0 ∨ i = 1 then .Z else .I

def logicalZ : Operator (Fin 4) :=
  fun i j => if i = j then if i.val < 2 then 1 else -1 else 0

theorem sitePauli_compression (site : Fin 4) (p : SinglePauli) :
    encoding.conjTranspose * pauliMatrix 0 (sitePauli site p) * encoding =
      if p = .I then 1 else 0 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a
  fin_cases b
  rw [encoding_compression_entry, scale_norm]
  fin_cases site <;> cases p <;> fin_cases i <;> fin_cases j <;>
    norm_num [sitePauli, pauliMatrix, word, complement, SinglePauli.matrix,
      Fin.prod_univ_succ, Matrix.one_apply]

theorem weightTwoPauli_compression :
    encoding.conjTranspose * pauliMatrix 0 weightTwoPauli * encoding =
      logicalZ ⊗ₖ (1 : Operator (Fin 1)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a
  fin_cases b
  rw [encoding_compression_entry, scale_norm]
  fin_cases i <;> fin_cases j <;>
    norm_num [weightTwoPauli, pauliMatrix, word, complement, SinglePauli.matrix,
      logicalZ, Matrix.kronecker_apply, Fin.prod_univ_succ]

theorem weightTwoPauli_supported :
    SupportedOn (pauliMatrix 0 weightTwoPauli) ({0, 1} : Finset (Fin 4)) := by
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp [weightTwoPauli, hi.1, hi.2]

theorem weightTwoPauli_nongauge : ¬ GaugeOnly code (pauliMatrix 0 weightTwoPauli) := by
  rintro ⟨M, hM⟩
  change encoding.conjTranspose * pauliMatrix 0 weightTwoPauli * encoding = _ at hM
  rw [weightTwoPauli_compression] at hM
  have h0 := congrArg (fun A : Operator (Fin 4 × Fin 1) => A (0, 0) (0, 0)) hM
  have h2 := congrArg (fun A : Operator (Fin 4 × Fin 1) => A (2, 0) (2, 0)) hM
  have hp : (1 : ℂ) = M 0 0 := by simpa [logicalZ, Matrix.kronecker_apply] using h0
  have hn : (-1 : ℂ) = M 0 0 := by simpa [logicalZ, Matrix.kronecker_apply] using h2
  have hh : (1 : ℂ) = -1 := hp.trans hn.symm
  norm_num at hh

/-- An actual supported, undetectable weight-two operator for this encoding. -/
theorem explicit_distance_witness :
    ∃ S : Finset (Fin 4), S.card = 2 ∧ ∃ O : Operator (QubitBasis 4),
      SupportedOn O S ∧ ¬ GaugeOnly code O := by
  exact ⟨{0, 1}, by decide, pauliMatrix 0 weightTwoPauli,
    weightTwoPauli_supported, weightTwoPauli_nongauge⟩

theorem sitePauli_gaugeOnly (site : Fin 4) (p : SinglePauli) :
    GaugeOnly code (pauliMatrix 0 (sitePauli site p)) := by
  refine ⟨if p = .I then 1 else 0, ?_⟩
  change encoding.conjTranspose * pauliMatrix 0 (sitePauli site p) * encoding = _
  rw [sitePauli_compression]
  by_cases hp : p = .I
  · simp [hp, Matrix.one_kronecker_one]
  · simp [hp]

theorem allIdentity_pauliMatrix : pauliMatrix (0 : Fin 4) (fun _ : Fin 4 => SinglePauli.I) = 1 := by
  rw [pauliMatrix_zero_eq_tensorEntries]
  exact tensorEntries_one

theorem detectsBelow_two : DetectsBelow code 2 := by
  classical
  intro S hS O hO
  obtain ⟨A, hA⟩ := hO
  let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin 4 => 2) S)) :=
    (gaugeOnlyComplexSubmodule code).comap (localEmbedLinearMap S)
  have hPauli : ∀ p : S → SinglePauli,
      GaugeOnly code (pauliMatrix 0 (extendLocalPauli S p)) := by
    intro p
    by_cases hempty : S = ∅
    · have hp : extendLocalPauli S p = fun _ => SinglePauli.I := by
        funext i
        simp [extendLocalPauli, hempty]
      rw [hp, allIdentity_pauliMatrix]
      refine ⟨1, ?_⟩
      simp [code, encoding_isometry, Matrix.one_kronecker_one]
    · have hcard : S.card = 1 := by
        have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        omega
      obtain ⟨site, hsite⟩ := Finset.card_eq_one.mp hcard
      have hsite_mem : site ∈ S := by rw [hsite]; simp
      let psite : SinglePauli := p ⟨site, hsite_mem⟩
      have hp : extendLocalPauli S p = sitePauli site psite := by
        funext i
        by_cases hi : i = site
        · subst i
          simp [extendLocalPauli, sitePauli, psite, hsite_mem]
        · have hiS : i ∉ S := by rw [hsite]; simpa using hi
          simp [extendLocalPauli, sitePauli, hi, hiS]
      rw [hp]
      exact sitePauli_gaugeOnly site psite
  have hspan : pauliTensorSpan S ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change GaugeOnly code (localEmbed S (tensorPauli p))
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    exact hPauli p
  rw [tensorPauli_span_eq_top] at hspan
  have hAB : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
  change GaugeOnly code (localEmbed S A) at hAB
  simpa only [hA] using hAB

theorem hasActualDistance_two : HasActualDistance code 2 :=
  ⟨detectsBelow_two, explicit_distance_witness⟩

end CriticalDepth.Manuscript.FourQubit
