import ShorNativeSaturation
import ShorFaultWitness
import ShorPhysicalXLogical
import FaultOnsetConsequence

/-!
# Ambiguity of the two Shor X-fault histories

A partition of a full logical X column gives two phase-free output errors.
Their product acts as the same nontrivial logical X on the encoding, so
any common terminal recovery incurs a uniform lower bound on its loss.
-/

namespace CriticalDepth.ShorFaultWitnessAmbiguity

noncomputable section

open CriticalDepth.Manuscript CriticalDepth.Arithmetic
open CriticalDepth.FaultShorSaturation CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryGeometry CriticalDepth.IndependentFaultHistories
open CriticalDepth.EncodedFaultRecovery CriticalDepth.FaultDepthArithmetic
open CriticalDepth.FaultProbability CriticalDepth.Manuscript20261114
open Filter Set Asymptotics
open scoped BigOperators ENat Kronecker Topology

variable {rows columns q h : ℕ}

private theorem binaryX_mul (a b : Bit) :
    (if a = 0 then SinglePauli.I else .X).matrix *
      (if b = 0 then SinglePauli.I else .X).matrix =
        (if a + b = 0 then SinglePauli.I else .X).matrix := by
  have hb : ∀ x : Bit, x = 0 ∨ x = 1 := by decide
  rcases hb a with (rfl | rfl) <;> rcases hb b with (rfl | rfl)
  · simp [SinglePauli.matrix]
  · simp [SinglePauli.matrix]
  · simp [SinglePauli.matrix]
  · have h : (1 : Bit) + 1 = 0 := by decide
    simp only [one_ne_zero, ite_false, h, ite_true, singlePauli_sq]
    rfl

/-- A physical site set and its rectangular binary mask induce the same
unphased X operator. -/
theorem fullX_eq_physicalXWord (s : Finset (Fin (rows * columns)))
    (a : Mask rows columns)
    (ha : ∀ i, i ∈ s ↔ a (shorSiteEquiv rows columns i) ≠ 0) :
    ShorFaultWitness.fullX s = pauliMatrix 0 (physicalXWord a) := by
  unfold ShorFaultWitness.fullX
  congr 1
  funext i
  by_cases hz : a (shorSiteEquiv rows columns i) = 0
  · have hi : i ∉ s := fun hmem => (ha i).mp hmem hz
    simp [physicalXWord, maskPauli, hz, hi]
  · have hi := (ha i).mpr hz
    simp [physicalXWord, maskPauli, hz, hi]

/-- Multiplication of X-only Pauli matrices has no scalar phase. -/
theorem physicalXWord_mul (a b : Mask rows columns) :
    pauliMatrix 0 (physicalXWord a) * pauliMatrix 0 (physicalXWord b) =
      pauliMatrix 0 (physicalXWord (a + b)) := by
  simp only [pauliMatrix_zero_eq_tensorEntries]
  rw [← tensorEntries_mul]
  apply congrArg (tensorEntriesMonoidHom (Fin (rows * columns)))
  funext i
  exact binaryX_mul (a (shorSiteEquiv rows columns i)) (b (shorSiteEquiv rows columns i))

private def logicalX : Operator (Fin 2 × Fin 1) :=
  SinglePauli.X.matrix ⊗ₖ (1 : Operator (Fin 1))

private theorem logicalX_unitary : IsUnitary logicalX :=
  point_kronecker_isUnitary SinglePauli.X.matrix 1 (singlePauli_isUnitary .X) isUnitary_one

private theorem logicalX_trace : logicalX.trace = 0 := by
  unfold logicalX
  rw [Matrix.trace_kronecker]
  have hX : SinglePauli.X.matrix.trace = 0 := by
    simp [SinglePauli.matrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rw [hX, zero_mul]

/-- Two output errors whose binary masks add to a full column differ by
logical X on the same encoding. -/
theorem encodedBranch_of_X_mask_partition (i : Fin rows) (j : Fin (columns + 1))
    (L : Layers (rows * (columns + 1)) q)
    (x y : History (fun t : Location L => FaultLabel t))
    (a b : Mask rows (columns + 1))
    (hx : outputHistory (insertion L) physicalFault x (chronologicalFaults x) =
      pauliMatrix 0 (physicalXWord a))
    (hy : outputHistory (insertion L) physicalFault y (chronologicalFaults y) =
      pauliMatrix 0 (physicalXWord b))
    (hab : a + b = fullXColumn j) :
    encodedBranch (physicalShorCode (columns := columns) i) y =
      encodedBranch (physicalShorCode (columns := columns) i) x * logicalX := by
  have hmul := physicalXWord_mul a b
  rw [hab] at hmul
  have henc := physicalShorEncoding_fullXColumn (rows := rows) (columns := columns) j
  change pauliMatrix 0 (physicalXWord (fullXColumn j)) * physicalShorEncoding rows columns =
    physicalShorEncoding rows columns * logicalX at henc
  unfold encodedBranch
  rw [hx, hy]
  change pauliMatrix 0 (physicalXWord b) * physicalShorEncoding rows columns =
    (pauliMatrix 0 (physicalXWord a) * physicalShorEncoding rows columns) * logicalX
  rw [Matrix.mul_assoc, ← henc, ← hmul, ← Matrix.mul_assoc]
  have hCancel : pauliMatrix 0 (physicalXWord a) *
      (pauliMatrix 0 (physicalXWord a) * pauliMatrix 0 (physicalXWord b)) =
        pauliMatrix 0 (physicalXWord b) := by
    rw [← Matrix.mul_assoc, unphased_pauliMatrix_sq, Matrix.one_mul]
  rw [hCancel]

/-- A phase-free logical X partition forces the two histories to differ,
including when the faulty locations lie in the same layer. -/
theorem distinct_of_X_mask_partition (i : Fin rows) (j : Fin (columns + 1))
    (L : Layers (rows * (columns + 1)) q)
    (x y : History (fun t : Location L => FaultLabel t))
    (a b : Mask rows (columns + 1))
    (hx : outputHistory (insertion L) physicalFault x (chronologicalFaults x) =
      pauliMatrix 0 (physicalXWord a))
    (hy : outputHistory (insertion L) physicalFault y (chronologicalFaults y) =
      pauliMatrix 0 (physicalXWord b))
    (hab : a + b = fullXColumn j) : x ≠ y := by
  intro hxy
  let C := physicalShorCode (columns := columns) i
  let A := encodedBranch C x
  have hh : A = A * logicalX := by
    have h := encodedBranch_of_X_mask_partition i j L x y a b hx hy hab
    rwa [← hxy] at h
  have hi : A.conjTranspose * A = 1 := encodedBranch_isometry C x
  have hh' := congrArg (fun M : Matrix (QubitBasis (rows * (columns + 1))) (Fin 2 × Fin 1) ℂ =>
    A.conjTranspose * M) hh
  rw [← Matrix.mul_assoc, hi, Matrix.one_mul] at hh'
  have h := logicalX_trace
  rw [← hh', Matrix.trace_one] at h
  norm_num at h

/-- Nonempty fault histories in different single layers are distinct. -/
theorem distinct_of_fault_layers {n q : ℕ} {L : Layers n q}
    {x y : History (fun t : Location L => FaultLabel t)}
    {early late : Fin L.length} (he : early ≠ late)
    (hx : 0 < (faults x).card)
    (hxlayer : ∀ z ∈ faults x, z.val.1 = early)
    (hylayer : ∀ z ∈ faults y, z.val.1 = late) : x ≠ y := by
  intro hxy
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hx
  exact he ((hxlayer z hz).symm.trans (hylayer z (hxy ▸ hz)))

theorem two_history_eventual_lower
    {Loc Phys Log : Type*} [Fintype Loc] [DecidableEq Loc] [Fintype Phys] [DecidableEq Phys]
    [Fintype Log] [DecidableEq Log] [Nonempty Log]
    {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (x y : History Label) (hxy : x ≠ y) (P : Matrix Log Log ℂ)
    (hP : P * P.conjTranspose = 1) (ht : P.trace = 0) (hattach : A y = A x * P) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
      c * p ^ max (faults x).card (faults y).card ≤ optimalInfidelity μ A p := by
  classical
  let w (z : History Label) := conditionalWeight μ z
  let k (z : History Label) := (faults z).card
  let clean (z : History Label) := Fintype.card Loc - k z
  let c := min (w x * (1 / 2 : ℝ) ^ clean x) (w y * (1 / 2 : ℝ) ^ clean y)
  have hc : 0 < c := lt_min
    (mul_pos (conditionalWeight_pos μ x) (pow_pos (by norm_num) _))
    (mul_pos (conditionalWeight_pos μ y) (pow_pos (by norm_num) _))
  refine ⟨c, hc, ?_⟩
  have hhalf : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_, by norm_num, subset_rfl⟩
  filter_upwards [hhalf] with p hp
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨R, rfl⟩
  have hnonneg (z : History Label) := (branchLoss_mem_Icc (A z) (hA z) R).1
  have hamb := FaultAmbiguity.twoHistory_loss_sum_ge_one
    (A x) (A y) R.kraus P (hA x) R.complete hP ht hattach
  have hpair := (twoHistoriesPowerLower p (w x) (w y) (branchLoss (A x) R) (branchLoss (A y) R)
    (k x) (k y) (clean x) (clean y) hp.1.le hp.2.le
    (conditionalWeight_pos μ x) (conditionalWeight_pos μ y)
    (hnonneg x) (hnonneg y) hamb).2
  change c * p ^ max (faults x).card (faults y).card ≤
    historyMass p (w x) (k x) (clean x) * branchLoss (A x) R +
      historyMass p (w y) (k y) (clean y) * branchLoss (A y) R at hpair
  rw [← mass_eq_historyMass μ p x, ← mass_eq_historyMass μ p y] at hpair
  apply hpair.trans
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun z => mass μ p z * branchLoss (A z) R)
    (Finset.subset_univ ({x, y} : Finset (History Label)))
    (fun z _ _ => mul_nonneg (mass_nonneg μ hp.1.le (by linarith [hp.2]) z) (hnonneg z))
  simpa [Finset.sum_pair hxy, FaultExponent.lossAt, expectedHistoryLoss] using hsum

/-- An actual pair of equal-order X mask histories establishes per-code
saturation and matching asymptotic bounds for that same circuit. -/
theorem physicalShorCode_saturates_of_X_mask_partition (i : Fin rows)
    (hside : columns + 1 ≤ rows) (hq : 1 ≤ q)
    (e : Experiment (physicalShorCode (columns := columns) i) q h)
    (x y : History (fun t : Location e.layers => FaultLabel t))
    (hxy : x ≠ y)
    (a b : Mask rows (columns + 1)) (j : Fin (columns + 1))
    (hx : outputHistory (insertion e.layers) physicalFault x (chronologicalFaults x) =
      pauliMatrix 0 (physicalXWord a))
    (hy : outputHistory (insertion e.layers) physicalFault y (chronologicalFaults y) =
      pauliMatrix 0 (physicalXWord b))
    (hab : a + b = fullXColumn j)
    (hcx : (faults x).card = lowerEnvelope q (columns + 1) h)
    (hcy : (faults y).card = lowerEnvelope q (columns + 1) h) :
    perCodeExponent (physicalShorCode (columns := columns) i) q h =
      (lowerEnvelope q (columns + 1) h : ℕ∞) ∧
    (circuitInfidelity (physicalShorCode (columns := columns) i) e.layers e.law
      =O[𝓝[>] 0] fun p => p ^ lowerEnvelope q (columns + 1) h) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ p in 𝓝[>] (0 : ℝ),
      c * p ^ lowerEnvelope q (columns + 1) h ≤
        circuitInfidelity (physicalShorCode (columns := columns) i) e.layers e.law p := by
  let C := physicalShorCode (columns := columns) i
  have hbranch := encodedBranch_of_X_mask_partition i j e.layers x y a b hx hy hab
  have hper := physicalShorCode_saturates_of_native_histories i hside hq e x y hxy
    logicalX logicalX_unitary.2 logicalX_trace hbranch hcx.le hcy.le
  have hupper := ambiguous_exponent_of_traceless_unitary e.law (encodedBranch C)
    (encodedBranch_isometry C) x y hxy logicalX logicalX_unitary.2 logicalX_trace hbranch
  rw [hcx, hcy, max_self] at hupper
  have hfloor : perCodeExponent C q h ≤
      FaultExponent.exponent (circuitInfidelity C e.layers e.law) := iInf_le _ e
  rw [hper] at hfloor
  have hopt : FaultExponent.exponent (circuitInfidelity C e.layers e.law) =
      (lowerEnvelope q (columns + 1) h : ℕ∞) := le_antisymm hupper hfloor
  have hm : 0 < lowerEnvelope q (columns + 1) h := ceilDiv_pos (by omega) _
  refine ⟨hper, FaultExponent.isBigO_of_exponent_eq hopt hm, ?_⟩
  have hlower := two_history_eventual_lower e.law (encodedBranch C) (encodedBranch_isometry C)
    x y hxy logicalX logicalX_unitary.2 logicalX_trace hbranch
  simpa only [hcx, hcy, max_self, circuitInfidelity, C] using hlower

#print axioms fullX_eq_physicalXWord
#print axioms physicalXWord_mul
#print axioms encodedBranch_of_X_mask_partition
#print axioms distinct_of_X_mask_partition
#print axioms distinct_of_fault_layers
#print axioms physicalShorCode_saturates_of_X_mask_partition

end
end CriticalDepth.ShorFaultWitnessAmbiguity
