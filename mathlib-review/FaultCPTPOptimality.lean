import FaultCPTPRepresentation
import FaultKrausCompression
import EncodedFaultRecovery

/-!
# Optimal entanglement infidelity over all terminal CPTP maps

The physical recovery is a complex-linear CPTP map. The same map acts
in every fault history, on the physical side of a reference-first Bell
state. The normalized state test gives the existing finite-Kraus loss,
and the minimum over all CPTP maps is attained.
-/

namespace CriticalDepth.FaultCPTPOptimality

noncomputable section

open Matrix Set
open scoped BigOperators Kronecker
open FaultEntanglementFidelity FaultCPTPRepresentation EncodedFaultRecovery
open IndependentFaultHistories

variable {Phys Log Rec : Type*}
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]

/-- The recovered channel for one encoded error isometry. -/
def recoverBranch (L : MatrixChannel Phys Log) (A : Matrix Phys Log ℂ) :
    MatrixChannel Log Log where
  toFun X := L (A * X * A.conjTranspose)
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply]

theorem recoverBranch_kraus [Fintype Rec] (R : Rec → Matrix Log Phys ℂ)
    (A : Matrix Phys Log ℂ) :
    recoverBranch (krausMap R) A = krausMap (fun k => R k * A) := by
  apply LinearMap.ext
  intro X
  change krausMap R (A * X * A.conjTranspose) = krausMap (fun k => R k * A) X
  simp only [krausMap_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Matrix element of the normalized target Bell state. Amplification acts
only on the encoded system, preserving the reference tensor factor. -/
def channelFidelity (L : MatrixChannel Log Log) : ℝ :=
  (star (bellVector (ι := Log)) ⬝ᵥ
    ((amplify L (bellProjector Log)) *ᵥ bellVector (ι := Log))).re / (Fintype.card Log : ℝ)

def channelBranchLoss (A : Matrix Phys Log ℂ) (L : MatrixChannel Phys Log) : ℝ :=
  1 - channelFidelity (recoverBranch L A)

private theorem amplified_krausMap [Fintype Rec] (R : Rec → Matrix Log Log ℂ)
    (X : Matrix (Log × Log) (Log × Log) ℂ) :
    amplify (krausMap R) X = ∑ k,
      ((1 : Matrix Log Log ℂ) ⊗ₖ R k) * X *
       (((1 : Matrix Log Log ℂ) ⊗ₖ R k)).conjTranspose := by
  apply Matrix.ext
  rintro ⟨r, a⟩ ⟨s, b⟩
  simp only [amplify, Matrix.of_apply, krausMap_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hLeft (j : Log × Log) :
      (((1 : Matrix Log Log ℂ) ⊗ₖ R k) * X) (r, a) j =
        ∑ i : Log, R k a i * X (r, i) j := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single r]
    · simp
    · intro t _ hne
      apply Finset.sum_eq_zero
      intro i _
      simp [Ne.symm hne]
    · simp
  conv_rhs => rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp only [hLeft, Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul,
      Matrix.mul_apply, Matrix.of_apply]
  · intro t _ hne
    apply Finset.sum_eq_zero
    intro i _
    simp [Ne.symm hne]
  · simp

theorem channelFidelity_kraus [Fintype Rec] (R : Rec → Matrix Log Log ℂ) :
    channelFidelity (krausMap R) = fidelity R := by
  unfold channelFidelity
  rw [amplified_krausMap]
  exact (fidelity_eq_bell_overlap R).symm

theorem channelBranchLoss_kraus [Fintype Rec] (R : Rec → Matrix Log Phys ℂ)
    (A : Matrix Phys Log ℂ) :
    channelBranchLoss A (krausMap R) = loss (fun k => R k * A) := by
  simp only [channelBranchLoss, recoverBranch_kraus, channelFidelity_kraus, loss]

/-- Recovery channels in the optimization include all CP, TP linear maps. -/
def RecoveryChannel (Phys Log : Type*) [Fintype Phys] [Fintype Log] :=
  {L : MatrixChannel Phys Log // IsCompletelyPositive L ∧ IsTracePreserving L}

private def fromKraus (R : TerminalRecovery Phys Log) : RecoveryChannel Phys Log :=
  ⟨krausMap R.kraus, kraus_isCompletelyPositive _,
    (kraus_isTracePreserving_iff _).mpr R.complete⟩

private theorem fromKraus_surjective :
    Function.Surjective (fromKraus (Phys := Phys) (Log := Log)) := by
  intro L
  obtain ⟨K, hEq, hTP⟩ := (cptp_iff_exists_completeKraus L.val).mp L.property
  let e := Fintype.equivFin (Phys × Log)
  let K' := K ∘ e.symm
  have hTP' : (∑ k, (K' k).conjTranspose * K' k) = 1 := by
    calc
      _ = ∑ k : Phys × Log, (K k).conjTranspose * K k :=
        e.symm.sum_comp (fun k => (K k).conjTranspose * K k)
      _ = 1 := hTP
  refine ⟨⟨_, K', hTP'⟩, Subtype.ext ?_⟩
  apply LinearMap.ext
  intro X
  change krausMap K' X = L.val X
  simp only [hEq, krausMap_apply]
  exact e.symm.sum_comp (fun k => K k * X * (K k).conjTranspose)

variable {Loc : Type*} [Fintype Loc] [DecidableEq Loc]
variable {Label : Loc → Type*} [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]

/-- Infidelity of the recovered noisy channel, averaged over its finite
unflagged histories with their native independent Pauli law. -/
def channelHistoryLoss (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (p : ℝ) (L : RecoveryChannel Phys Log) : ℝ :=
  ∑ x, mass μ p x * channelBranchLoss (A x) L.val

theorem channelHistoryLoss_eq_kraus (μ : Law Label) (A : History Label → Matrix Phys Log ℂ)
    (p : ℝ) (R : TerminalRecovery Phys Log) :
    channelHistoryLoss μ A p (fromKraus R) =
      FaultExponent.lossAt μ (fun x => branchLoss (A x)) p R := by
  simp [channelHistoryLoss, fromKraus, channelBranchLoss_kraus, branchLoss,
    FaultExponent.lossAt, Manuscript20261114.expectedHistoryLoss]

/-- The infimum over all terminal CPTP maps exactly equals the finite
Kraus optimization used for the circuit's exponent. -/
theorem optimalInfidelity_eq_cptp_inf (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (p : ℝ) :
    optimalInfidelity μ A p = sInf (Set.range (channelHistoryLoss μ A p)) := by
  unfold optimalInfidelity FaultExponent.optimalLoss
  congr 1
  ext ε
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨fromKraus R, channelHistoryLoss_eq_kraus μ A p R⟩
  · rintro ⟨L, rfl⟩
    obtain ⟨R, rfl⟩ := fromKraus_surjective L
    exact ⟨R, (channelHistoryLoss_eq_kraus μ A p R).symm⟩

/-- A common CPTP terminal recovery attains the optimum, for every noise
parameter and each fixed encoded fault ensemble. -/
theorem exists_cptp_optimalInfidelity (μ : Law Label)
    (A : History Label → Matrix Phys Log ℂ) (p : ℝ) :
    ∃ L : RecoveryChannel Phys Log, channelHistoryLoss μ A p L = optimalInfidelity μ A p := by
  obtain ⟨R, hR, hOpt⟩ := FaultKrausCompression.exists_minimum_all_finiteKraus
    Finset.univ (mass μ p) A
  let L : RecoveryChannel Phys Log := ⟨krausMap R, kraus_isCompletelyPositive _,
    (kraus_isTracePreserving_iff _).mpr hR⟩
  refine ⟨L, ?_⟩
  rw [optimalInfidelity_eq_cptp_inf]
  apply le_antisymm
  · apply le_csInf ⟨_, Set.mem_range_self L⟩
    rintro _ ⟨L', rfl⟩
    obtain ⟨T, rfl⟩ := fromKraus_surjective L'
    rw [channelHistoryLoss_eq_kraus]
    have ht := hOpt T.count T.kraus T.complete
    simpa [L, channelHistoryLoss, channelBranchLoss_kraus, FaultExponent.lossAt,
      Manuscript20261114.expectedHistoryLoss, branchLoss] using ht
  · apply csInf_le _ (Set.mem_range_self L)
    refine ⟨channelHistoryLoss μ A p L, ?_⟩
    rintro _ ⟨L', rfl⟩
    obtain ⟨T, rfl⟩ := fromKraus_surjective L'
    rw [channelHistoryLoss_eq_kraus]
    have ht := hOpt T.count T.kraus T.complete
    simpa [L, channelHistoryLoss, channelBranchLoss_kraus, FaultExponent.lossAt,
      Manuscript20261114.expectedHistoryLoss, branchLoss] using ht

#print axioms recoverBranch_kraus
#print axioms channelFidelity_kraus
#print axioms channelBranchLoss_kraus
#print axioms optimalInfidelity_eq_cptp_inf
#print axioms exists_cptp_optimalInfidelity

end

end CriticalDepth.FaultCPTPOptimality
