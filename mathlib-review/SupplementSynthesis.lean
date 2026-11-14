import BarePauliRotations
import GenerationThresholds

/-!
# Depth bounds for a prescribed logical Pauli frame

Each member of a finite family can be synthesized at the maximum of its
compression depths. If the corresponding logical rotations generate the
full projective unitary group by finite words, the same bound applies to
the exact-generation threshold.
-/

open scoped Kronecker

namespace CriticalDepth.Manuscript20261114

open Manuscript ReviewV2

noncomputable section

variable {n K : ℕ}

/-- The compression depth is monotone in the weight bound. -/
theorem criticalDepth_mono_weight (q : ℕ) {a b : ℕ} (hab : a ≤ b) :
    Arithmetic.criticalDepth q a ≤ Arithmetic.criticalDepth q b := by
  have h := Nat.clog_mono_right q hab
  unfold Arithmetic.criticalDepth
  omega

theorem one_le_criticalDepth_of_two_le (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    1 ≤ Arithmetic.criticalDepth q d := by
  have h := Nat.clog_pos (b := q) (n := d) (by omega) (by omega)
  unfold Arithmetic.criticalDepth
  omega

/-- Chosen physical Hermitian Pauli representatives of a finite family of
logical involutions. The logical matrix includes the sign of the chosen
unphased physical Pauli; either rotation direction gives the same alphabet
because the angle ranges over all real numbers. -/
structure PauliRotationFamily (C : Code n (fun _ => 2) K 1) (ι : Type*) where
  physical : ι → Fin n → SinglePauli
  logical : ι → Operator (Fin K)
  encoded : ∀ i, pauliMatrix (0 : Fin 4) (physical i) * C.encoding =
    C.encoding * (logical i ⊗ₖ (1 : Operator (Fin 1)))
  selfAdjoint : ∀ i, star (logical i) = logical i
  squareOne : ∀ i, logical i * logical i = 1

variable {C : Code n (fun _ => 2) K 1} {ι : Type*}

def PauliRotationFamily.alphabet (F : PauliRotationFamily C ι) : Set (PU (Fin K)) :=
  {U | ∃ (i : ι) (t : ℝ), projectiveRotation (F.logical i)
    (F.selfAdjoint i) (F.squareOne i) t = U}

def PauliRotationFamily.maxWeight [Fintype ι] (F : PauliRotationFamily C ι) : ℕ :=
  Finset.univ.sup (fun i => (pauliSupport (F.physical i)).card)

theorem PauliRotationFamily.weight_le_maxWeight [Fintype ι] (F : PauliRotationFamily C ι)
    (i : ι) : (pauliSupport (F.physical i)).card ≤ F.maxWeight := by
  unfold PauliRotationFamily.maxWeight
  exact Finset.le_sup (f := fun j => (pauliSupport (F.physical j)).card) (Finset.mem_univ i)

/-- The actual code distance lower-bounds the weight of a nonscalar bare
logical Pauli representative. -/
theorem weight_ge_distance_of_nonscalar_logical
    (d : ℕ) (hd : DetectsBelow C d) (p : Fin n → SinglePauli) (A : Operator (Fin K))
    (henc : pauliMatrix (0 : Fin 4) p * C.encoding =
      C.encoding * (A ⊗ₖ (1 : Operator (Fin 1))))
    (hnon : ¬ IsScalar A) :
    d ≤ (pauliSupport p).card := by
  by_contra! hsmall
  obtain ⟨M, hM⟩ := hd (pauliSupport p) hsmall _ (pauliMatrix_supportedOn_pauliSupport p)
  have hcompress : C.encoding.conjTranspose * pauliMatrix (0 : Fin 4) p * C.encoding =
      A ⊗ₖ (1 : Operator (Fin 1)) := by
    rw [Matrix.mul_assoc, henc, ← Matrix.mul_assoc, C.isometry, Matrix.one_mul]
  rw [hcompress] at hM
  apply hnon
  use M 0 0
  ext i j
  have hij := congrArg (fun Q : Operator (Fin K × Fin 1) => Q (i, 0) (j, 0)) hM
  simpa [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using hij

/-- Every chosen direction has a physical generator at the common budget. -/
theorem PauliRotationFamily.alphabet_subset_nativeLogicalImage [Fintype ι]
    (F : PauliRotationFamily C ι) (hn : 0 < n) (q : ℕ) (hq : 2 ≤ q)
    (hD : 2 ≤ F.maxWeight) :
    F.alphabet ⊆ nativeLogicalImage C.encoding q (Arithmetic.criticalDepth q F.maxWeight) := by
  rintro _ ⟨i, t, rfl⟩
  apply nativeLogicalImage_mono_depth C.encoding q
    (i := max 1 (Arithmetic.criticalDepth q (pauliSupport (F.physical i)).card))
  · apply max_le (one_le_criticalDepth_of_two_le q F.maxWeight hq hD)
    exact criticalDepth_mono_weight q (F.weight_le_maxWeight i)
  exact barePauli_projectiveRotation_mem_nativeLogicalImage C hn q hq
    (F.physical i) (F.logical i) (F.encoded i) (F.selfAdjoint i) (F.squareOne i) t

theorem PauliRotationFamily.maxWeight_le_n [Fintype ι] (F : PauliRotationFamily C ι) :
    F.maxWeight ≤ n := by
  apply Finset.sup_le
  intro i _
  simpa using (Finset.card_le_univ (s := pauliSupport (F.physical i)))

/-- Physical compression lifts finite-word logical universality to the
stabilizer depth bounds. The finite-word condition is the separate logical
synthesis obligation for the tree frame in the manuscript. -/
theorem exact_generator_depth_bounds_of_logical_generation {k d : ℕ} [Fintype ι]
    [Nonempty ι] (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hk : 1 ≤ k) (hd : 2 ≤ d) (q : ℕ) (hq : 2 ≤ q)
    (hstab : IsStabilizer C) (hdist : HasActualDistance C d)
    (F : PauliRotationFamily C ι) (hF : ∀ i, ¬ IsScalar (F.logical i))
    (hGen : Subgroup.closure F.alphabet = ⊤) :
    (Arithmetic.criticalDepth q d : ℕ∞) ≤ nativeExactDepth C.encoding q ∧
      nativeExactDepth C.encoding q ≤ (Arithmetic.criticalDepth q F.maxWeight : ℕ∞) ∧
      Arithmetic.criticalDepth q F.maxWeight ≤ Arithmetic.criticalDepth q n := by
  classical
  let i : ι := Classical.choice inferInstance
  have hdD : d ≤ F.maxWeight :=
    (weight_ge_distance_of_nonscalar_logical d hdist.1 (F.physical i) (F.logical i)
      (F.encoded i) (hF i)).trans (F.weight_le_maxWeight i)
  have hD : 2 ≤ F.maxWeight := hd.trans hdD
  have hn : 0 < n := by
    have hDn := F.maxWeight_le_n
    omega
  have hK : 2 ≤ 2 ^ k := by
    exact Nat.one_lt_pow (by omega) (by decide)
  have hOnset : nativeCriticalDepth C.encoding q = (Arithmetic.criticalDepth q d : ℕ∞) :=
    (nativeCriticalDepth_eq_legacy C.encoding C.isometry q).trans
      (theoremTwoPositive_proved n k d q hk hd hq C hstab hdist).1
  have hLowerTop := max_nativeCriticalDepth_nativeDenseDepth_le_nativeExactDepth C.encoding q hK
  have hLower : (Arithmetic.criticalDepth q d : ℕ∞) ≤ nativeExactDepth C.encoding q :=
    hOnset ▸ (le_max_left _ _).trans hLowerTop
  refine ⟨hLower, ?_, criticalDepth_mono_weight q F.maxWeight_le_n⟩
  apply (nativeExactDepth_le_nat_iff C.encoding q _).mpr
  refine ⟨one_le_criticalDepth_of_two_le q F.maxWeight hq hD, ?_⟩
  apply top_unique
  rw [← hGen]
  exact Subgroup.closure_mono (F.alphabet_subset_nativeLogicalImage hn q hq hD)

end

end CriticalDepth.Manuscript20261114
