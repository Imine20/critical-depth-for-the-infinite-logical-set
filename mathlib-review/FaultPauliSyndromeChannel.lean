import FaultCPTPOptimality
import PauliSyndromeOptimization
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Optimal terminal recovery for orthogonal syndrome sectors

The channel error branches are the sector isometries followed by logical
unitaries. A complete trace-orthogonal unitary basis gives the exact
sum of recovery fidelities within each sector.
-/

namespace CriticalDepth.FaultPauliSyndromeChannel

noncomputable section

open Matrix Module
open CriticalDepth.FaultEntanglementFidelity CriticalDepth.FaultCPTPRepresentation
open CriticalDepth.FaultCPTPOptimality CriticalDepth.EncodedFaultRecovery
open CriticalDepth.Manuscript20261114 CriticalDepth.Manuscript
open scoped BigOperators

variable {Phys Log Syndrome Label Rec : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]
variable [Fintype Syndrome] [Fintype Label] [DecidableEq Label] [Fintype Rec]

/-- The Pauli basis is characterized by its orthogonal trace pairing. The
basis is written as adjoints of the unitaries used on actual branches. -/
def TraceOrthogonalUnitaryBasis (b : Basis Label ℂ (Matrix Log Log ℂ)) : Prop :=
  (∀ l, IsUnitary (b l)) ∧ ∀ l j,
    ((b l).conjTranspose * b j).trace = if l = j then (Fintype.card Log : ℂ) else 0

private theorem basis_trace_coordinate (b : Basis Label ℂ (Matrix Log Log ℂ))
    (hb : TraceOrthogonalUnitaryBasis b) (A : Matrix Log Log ℂ) (j : Label) :
    ((b j).conjTranspose * A).trace = (Fintype.card Log : ℂ) * b.repr A j := by
  classical
  conv_lhs => rw [← b.sum_repr A]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, hb.2]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro i _ hne
    simp [Ne.symm hne]
  · simp

private theorem unitary_trace_parseval (b : Basis Label ℂ (Matrix Log Log ℂ))
    (hb : TraceOrthogonalUnitaryBasis b) (A : Matrix Log Log ℂ) :
    (∑ j, Complex.normSq (A * (b j).conjTranspose).trace) =
      (Fintype.card Log : ℝ) * (A.conjTranspose * A).trace.re := by
  classical
  let D := (Fintype.card Log : ℝ)
  have hpair (j : Label) : ((b j).conjTranspose * A).trace = (D : ℂ) * b.repr A j := by
    simpa [D] using basis_trace_coordinate b hb A j
  have hpair' (j : Label) : (A.conjTranspose * b j).trace = (D : ℂ) * star (b.repr A j) := by
    have h := congrArg (star : ℂ → ℂ) (hpair j)
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, star_mul] at h
    simpa [mul_comm] using h
  have htrace : (A.conjTranspose * A).trace =
      ∑ j, b.repr A j * ((D : ℂ) * star (b.repr A j)) := by
    conv_lhs =>
      arg 1
      arg 2
      rw [← b.sum_repr A]
    simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, hpair']
  have hre := congrArg Complex.re htrace
  have hreal : (A.conjTranspose * A).trace.re =
      ∑ j, D * Complex.normSq (b.repr A j) := by
    rw [Complex.re_sum] at hre
    rw [hre]
    apply Finset.sum_congr rfl
    intro j _
    rw [show b.repr A j * ((D : ℂ) * star (b.repr A j)) =
      (D : ℂ) * (star (b.repr A j) * b.repr A j) by ring]
    change ((D : ℂ) * ((starRingEnd ℂ) (b.repr A j) * b.repr A j)).re = _
    rw [← Complex.normSq_eq_conj_mul_self]
    simp
  rw [hreal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.trace_mul_comm, hpair, Complex.normSq_mul]
  simp [D, mul_assoc]

/-- Within each syndrome the fidelities of all logical Pauli classes sum to one,
for an arbitrary complete finite Kraus recovery. -/
theorem syndrome_fidelity_sum (b : Basis Label ℂ (Matrix Log Log ℂ))
    (hb : TraceOrthogonalUnitaryBasis b) (A : Matrix Phys Log ℂ)
    (hA : A.conjTranspose * A = 1) (R : Rec → Matrix Log Phys ℂ)
    (hR : (∑ k, (R k).conjTranspose * R k) = 1) :
    ∑ l, fidelity (fun k => R k * (A * (b l).conjTranspose)) = 1 := by
  let D := (Fintype.card Log : ℝ)
  have hD : D ≠ 0 := by
    change (Fintype.card Log : ℝ) ≠ 0
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Log).ne'
  have hTP : (∑ k, (R k * A).conjTranspose * (R k * A)) = 1 := by
    calc
      _ = A.conjTranspose * (∑ k, (R k).conjTranspose * R k) * A := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hR, Matrix.mul_one, hA]
  have hTrace : (∑ k, ((R k * A).conjTranspose * (R k * A)).trace.re) = D := by
    have h := congrArg (fun M : Matrix Log Log ℂ => M.trace.re) hTP
    simpa [D, Matrix.trace_sum, Complex.re_sum] using h
  change (∑ l, (∑ k, Complex.normSq (R k * (A * (b l).conjTranspose)).trace) / D ^ 2) = 1
  simp only [← Matrix.mul_assoc, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [unitary_trace_parseval b hb]
  rw [← Finset.mul_sum, hTrace, ← pow_two, div_self (pow_ne_zero 2 hD)]

/-- The true entanglement loss of a recovered syndrome mixture. -/
def syndromeChannelLoss (A : Syndrome → Matrix Phys Log ℂ)
    (b : Basis Label ℂ (Matrix Log Log ℂ)) (q : Syndrome → Label → ℝ)
    (R : RecoveryChannel Phys Log) : ℝ :=
  ∑ s, ∑ l, q s l * channelBranchLoss (A s * (b l).conjTranspose) R.val

private theorem completeKraus_conditioned
    (A : Syndrome → Matrix Phys Log ℂ)
    (hA : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0)
    (b : Basis Label ℂ (Matrix Log Log ℂ)) (hb : TraceOrthogonalUnitaryBasis b)
    (selected : Syndrome → Label) :
    ∃ R : Syndrome ⊕ Phys → Matrix Log Phys ℂ,
      (∑ k, (R k).conjTranspose * R k) = 1 ∧
      ∀ s l, fidelity (fun k => R k * (A s * (b l).conjTranspose)) =
        if l = selected s then 1 else 0 := by
  classical
  let B (s : Syndrome) := A s * (b (selected s)).conjTranspose
  have hB (s : Syndrome) : (B s).conjTranspose * B s = 1 := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (A s).conjTranspose, hA s,
      Matrix.one_mul]
    exact (hb.1 (selected s)).2
  have hBo (s t : Syndrome) (hst : s ≠ t) : (B s).conjTranspose * B t = 0 := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (A s).conjTranspose, horth s t hst,
      Matrix.zero_mul, Matrix.mul_zero]
  let i := Classical.choice (inferInstance : Nonempty Log)
  obtain ⟨R, hR, z, hz⟩ := OrthogonalRecovery.existsRecoveryKraus_scalar
    B (Pi.single i 1) hB hBo (by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp)
  have hBA (s : Syndrome) : B s * b (selected s) = A s := by
    have hUnit : (b (selected s)).conjTranspose * b (selected s) = 1 :=
      (hb.1 (selected s)).1
    unfold B
    rw [Matrix.mul_assoc, hUnit, Matrix.mul_one]
  have hzNorm (s : Syndrome) : (∑ k, Complex.normSq (z k s)) = 1 := by
    have hComplete : (∑ k, (R k * B s).conjTranspose * (R k * B s)) = 1 := by
      calc
        _ = (B s).conjTranspose * (∑ k, (R k).conjTranspose * R k) * B s := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hR, Matrix.mul_one, hB s]
    have h := congrArg (fun M : Matrix Log Log ℂ => M i i) hComplete
    rw [Matrix.sum_apply, Matrix.one_apply_eq] at h
    have hk (k : Syndrome ⊕ Phys) :
        ((R k * B s).conjTranspose * (R k * B s)) i i = (Complex.normSq (z k s) : ℂ) := by
      rw [hz k s, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.mul_one, smul_smul, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one]
      change (starRingEnd ℂ) (z k s) * z k s = _
      exact (Complex.normSq_eq_conj_mul_self).symm
    simp only [hk] at h
    exact_mod_cast h
  refine ⟨R, hR, ?_⟩
  intro s l
  unfold fidelity
  let D := (Fintype.card Log : ℝ)
  change (∑ k, Complex.normSq (R k * (A s * (b l).conjTranspose)).trace) / D ^ 2 = _
  have hD : D ≠ 0 := by
    change (Fintype.card Log : ℝ) ≠ 0
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Log).ne'
  have hcomp (k : Syndrome ⊕ Phys) :
      R k * (A s * (b l).conjTranspose) = z k s • (b (selected s) * (b l).conjTranspose) := by
    rw [← hBA s, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hz, Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_mul]
  simp only [hcomp, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm
    (b (selected s)) ((b l).conjTranspose), hb.2]
  by_cases hs : l = selected s
  · simp only [hs, ite_true, Complex.normSq_mul, ← Finset.sum_mul, hzNorm, one_mul]
    rw [show Complex.normSq (Fintype.card Log : ℂ) = D ^ 2 by
      simpa only [D, Complex.ofReal_natCast, pow_two] using (Complex.normSq_ofReal (Fintype.card Log : ℝ))]
    exact div_self (pow_ne_zero 2 hD)
  · simp [hs, D]

private theorem syndromeChannelLoss_kraus
    (A : Syndrome → Matrix Phys Log ℂ)
    (b : Basis Label ℂ (Matrix Log Log ℂ)) (q : Syndrome → Label → ℝ)
    (hq : ∑ s, ∑ l, q s l = 1)
    (K : Rec → Matrix Log Phys ℂ) (hK : (∑ k, (K k).conjTranspose * K k) = 1) :
    syndromeChannelLoss A b q
      ⟨krausMap K, kraus_isCompletelyPositive _, (kraus_isTracePreserving_iff _).mpr hK⟩ =
      1 - ∑ s, ∑ l, q s l * fidelity (fun k => K k * (A s * (b l).conjTranspose)) := by
  simp only [syndromeChannelLoss, channelBranchLoss_kraus, loss, mul_sub, mul_one,
    Finset.sum_sub_distrib, hq]

/-- Exact optimum and an attaining channel. The formula applies to the
original finite mixture, whose branches are the matrices A_s P_l. -/
theorem syndromeChannelLoss_optimum
    (A : Syndrome → Matrix Phys Log ℂ)
    (hA : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0)
    (b : Basis Label ℂ (Matrix Log Log ℂ)) (hb : TraceOrthogonalUnitaryBasis b)
    (q : Syndrome → Label → ℝ) (hq : ∑ s, ∑ l, q s l = 1)
    (selected : Syndrome → Label) (hselected : ∀ s l, q s l ≤ q s (selected s)) :
    (∀ R : RecoveryChannel Phys Log,
      1 - ∑ s, q s (selected s) ≤ syndromeChannelLoss A b q R) ∧
    ∃ R : RecoveryChannel Phys Log,
      syndromeChannelLoss A b q R = 1 - ∑ s, q s (selected s) := by
  classical
  constructor
  · intro R
    obtain ⟨K, heq, hK⟩ := (cptp_iff_exists_completeKraus R.val).mp R.property
    have hR : R = ⟨krausMap K, kraus_isCompletelyPositive _,
        (kraus_isTracePreserving_iff _).mpr hK⟩ := Subtype.ext heq
    rw [hR, syndromeChannelLoss_kraus A b q hq K hK]
    apply sub_le_sub_left
    exact (syndromeSuccess_optimum q selected hselected).1
      (fun s l => fidelity (fun k => K k * (A s * (b l).conjTranspose)))
      (fun s l => div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (sq_nonneg _))
      (fun s => syndrome_fidelity_sum b hb (A s) (hA s) K hK)
  · obtain ⟨R, hR, hfaith⟩ := completeKraus_conditioned A hA horth b hb selected
    refine ⟨⟨krausMap R, kraus_isCompletelyPositive _, (kraus_isTracePreserving_iff _).mpr hR⟩, ?_⟩
    rw [syndromeChannelLoss_kraus A b q hq R hR]
    simp only [hfaith]
    rw [(syndromeSuccess_optimum q selected hselected).2]

theorem syndromeChannelLoss_sInf
    (A : Syndrome → Matrix Phys Log ℂ)
    (hA : ∀ s, (A s).conjTranspose * A s = 1)
    (horth : ∀ s t, s ≠ t → (A s).conjTranspose * A t = 0)
    (b : Basis Label ℂ (Matrix Log Log ℂ)) (hb : TraceOrthogonalUnitaryBasis b)
    (q : Syndrome → Label → ℝ) (hq : ∑ s, ∑ l, q s l = 1)
    (selected : Syndrome → Label) (hselected : ∀ s l, q s l ≤ q s (selected s)) :
    sInf (Set.range (syndromeChannelLoss A b q)) = 1 - ∑ s, q s (selected s) := by
  obtain ⟨hlower, R, hR⟩ := syndromeChannelLoss_optimum A hA horth b hb q hq selected hselected
  refine le_antisymm ?_ ?_
  · rw [← hR]
    exact csInf_le ⟨1 - ∑ s, q s (selected s), by rintro _ ⟨R', rfl⟩; exact hlower R'⟩
      (Set.mem_range_self R)
  · apply le_csInf ⟨_, Set.mem_range_self R⟩
    rintro _ ⟨R', rfl⟩
    exact hlower R'

#print axioms syndrome_fidelity_sum
#print axioms syndromeChannelLoss_optimum
#print axioms syndromeChannelLoss_sInf

end
end CriticalDepth.FaultPauliSyndromeChannel
