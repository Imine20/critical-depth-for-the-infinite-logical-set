import FaultDiamondTail
import FaultNativeModel

/-!
The local-stochastic union bound on logical error for arbitrary normalized
finite history weights, with one common terminal recovery.
-/

namespace CriticalDepth.FaultChannelEffects

noncomputable section

open Matrix CriticalDepth.Arithmetic CriticalDepth.Manuscript
open CriticalDepth.FaultCPTPRepresentation CriticalDepth.FaultCPTPOptimality
open CriticalDepth.EncodedFaultRecovery CriticalDepth.IndependentFaultHistories
open CriticalDepth.FaultDepthArithmetic CriticalDepth.FaultNativeModel
open CriticalDepth.FaultHistoryGeometry CriticalDepth.FaultCircuitSupport
open scoped BigOperators Kronecker ComplexOrder

variable {Hist Loc Phys Log : Type*}
variable [Fintype Hist] [DecidableEq Loc]
variable [Fintype Phys] [DecidableEq Phys] [Fintype Log] [DecidableEq Log] [Nonempty Log]

/-- A normalized finite distribution whose joint fault masses satisfy
the local-stochastic inequality at each set of locations. -/
structure LocalStochasticMass (locations : Finset Loc) (faultSet : Hist → Finset Loc)
    (p : ℝ) where
  weight : Hist → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1
  locations_subset : ∀ x, faultSet x ⊆ locations
  joint : ∀ s ⊆ locations,
    ∑ x ∈ Finset.univ.filter (fun x => s ⊆ faultSet x), weight x ≤ p ^ s.card

def recoveredMassChannel (weight : Hist → ℝ) (A : Hist → Matrix Phys Log ℂ)
    (R : RecoveryChannel Phys Log) : MatrixChannel Log Log :=
  ∑ x, (weight x : ℂ) • recoverBranch R.val (A x)

private theorem recoveredMassChannel_isCPTP {weight : Hist → ℝ}
    (hw : ∀ x, 0 ≤ weight x) (hn : ∑ x, weight x = 1)
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (R : RecoveryChannel Phys Log) :
    IsCompletelyPositive (recoveredMassChannel weight A R) ∧
      IsTracePreserving (recoveredMassChannel weight A R) := by
  have hBranch (x : Hist) := recoverBranch_isCPTP (A x) (hA x) R
  constructor
  · intro n X hX
    unfold recoveredMassChannel
    rw [amplify_sum]
    apply Matrix.posSemidef_sum
    intro x _
    rw [amplify_smul]
    exact (hBranch x).1 n X hX |>.smul
      (Complex.nonneg_iff.mpr ⟨by simpa using hw x, by simp⟩)
  · intro X
    simp only [recoveredMassChannel, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    have hsum : (∑ x, (weight x : ℂ)) = 1 := by exact_mod_cast hn
    calc
      _ = ∑ x, (weight x : ℂ) * X.trace := by
        apply Finset.sum_congr rfl
        intro x _
        rw [(hBranch x).2 X]
      _ = X.trace := by rw [← Finset.sum_mul, hsum, one_mul]

private theorem halfDiamond_mass_le_tail (weight : Hist → ℝ)
    (hw : ∀ x, 0 ≤ weight x) (hn : ∑ x, weight x = 1)
    (faultSet : Hist → Finset Loc) (m : ℕ)
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (R : RecoveryChannel Phys Log)
    (hR : ∀ x, (faultSet x).card < m → recoverBranch R.val (A x) = LinearMap.id) :
    halfDiamondByEffects (recoveredMassChannel weight A R) ≤
      ∑ x ∈ Finset.univ.filter (fun x => m ≤ (faultSet x).card), weight x := by
  classical
  let bad := Finset.univ.filter (fun x => m ≤ (faultSet x).card)
  apply real_sSup_le_of_nonneg
  · rintro _ ⟨n, X, E, hX, hE, rfl⟩
    have hsum : (∑ x, (weight x : ℂ)) = 1 := by exact_mod_cast hn
    have he :
        amplify (recoveredMassChannel weight A R) X - X =
          ∑ x, (weight x : ℂ) • (amplify (recoverBranch R.val (A x)) X - X) := by
      unfold recoveredMassChannel
      rw [amplify_sum]
      simp_rw [amplify_smul, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    have he' :
        amplify (recoveredMassChannel weight A R) X - X =
          ∑ x ∈ bad, (weight x : ℂ) • (amplify (recoverBranch R.val (A x)) X - X) := by
      rw [he]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      have hlt : (faultSet x).card < m :=
        Nat.lt_of_not_ge (fun h => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      rw [hR x hlt, amplify_id, sub_self, smul_zero]
    have hval (s : Finset Hist) (f : Hist → Matrix (Fin n × Log) (Fin n × Log) ℂ) :
        effectValue E (∑ x ∈ s, f x) = ∑ x ∈ s, effectValue E (f x) := by
      induction s using Finset.induction_on with
      | empty => simp [effectValue]
      | @insert x s hx ih => rw [Finset.sum_insert hx, effectValue_add, ih, Finset.sum_insert hx]
    rw [he', hval]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro x _
    rw [effectValue_smul, abs_mul, abs_of_nonneg (hw x)]
    have hx := recoverBranch_isCPTP (A x) (hA x) R
    exact mul_le_of_le_one_right (hw x)
      (effectValue_difference_abs_le_one hE (amplify_preserves_density _ hx.1 hx.2 n hX) hX)
  · exact Finset.sum_nonneg fun x _ => hw x

def optimalMassEntanglementInfidelity (weight : Hist → ℝ)
    (A : Hist → Matrix Phys Log ℂ) : ℝ :=
  sInf (Set.range fun R : RecoveryChannel Phys Log =>
    1 - channelFidelity (recoveredMassChannel weight A R))

def optimalMassHalfDiamond (weight : Hist → ℝ) (A : Hist → Matrix Phys Log ℂ) : ℝ :=
  sInf (Set.range fun R : RecoveryChannel Phys Log =>
    halfDiamondByEffects (recoveredMassChannel weight A R))

/-- Exact correction of every lower-weight branch bounds both independently
optimized error measures under any normalized local-stochastic law. -/
theorem localStochastic_recovery_bounds [DecidableEq Hist]
    (locations : Finset Loc) (faultSet : Hist → Finset Loc) (p : ℝ)
    (μ : LocalStochasticMass locations faultSet p)
    (A : Hist → Matrix Phys Log ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1)
    (m : ℕ) (hscalar : ∀ x y, (faultSet x).card < m → (faultSet y).card < m →
      ∃ z : ℂ, (A x).conjTranspose * A y = z • (1 : Matrix Log Log ℂ)) :
    optimalMassEntanglementInfidelity μ.weight A ≤ (locations.card.choose m : ℝ) * p ^ m ∧
      optimalMassHalfDiamond μ.weight A ≤ (locations.card.choose m : ℝ) * p ^ m := by
  classical
  let Good := {x : Hist // (faultSet x).card < m}
  let B (x : Good) := A x.val
  obtain ⟨T, hT⟩ := (common_zero_loss_iff B (fun x => hA x.val)).mpr
    (fun x y => hscalar x.val y.val x.property y.property)
  let R := fromKraus T
  have hcorrect (x : Hist) (hx : (faultSet x).card < m) :
      recoverBranch R.val (A x) = LinearMap.id :=
    recoverBranch_eq_id_of_zero_loss (A x) (hA x) T (hT ⟨x, hx⟩)
  have htail := FaultProbability.localStochasticTail Finset.univ locations faultSet μ.weight m p
    (fun x _ => μ.nonnegative x) (fun x _ => μ.locations_subset x) μ.joint
  have hd := (halfDiamond_mass_le_tail μ.weight μ.nonnegative μ.normalized faultSet m A hA R
    hcorrect).trans htail
  have hC (S : RecoveryChannel Phys Log) :=
    recoveredMassChannel_isCPTP μ.nonnegative μ.normalized A hA S
  have hbE : BddBelow (Set.range fun S : RecoveryChannel Phys Log =>
      1 - channelFidelity (recoveredMassChannel μ.weight A S)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨S, rfl⟩
    obtain ⟨K, hK, hTP⟩ := (cptp_iff_exists_completeKraus _).mp (hC S)
    change 0 ≤ 1 - channelFidelity (recoveredMassChannel μ.weight A S)
    rw [hK, channelFidelity_kraus]
    exact FaultEntanglementFidelity.loss_nonneg K hTP
  have hbD : BddBelow (Set.range fun S : RecoveryChannel Phys Log =>
      halfDiamondByEffects (recoveredMassChannel μ.weight A S)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact Real.sSup_nonneg (by rintro _ ⟨_, _, _, _, _, rfl⟩; exact abs_nonneg _)
  constructor
  · exact (csInf_le hbE (Set.mem_range_self R)).trans
      ((loss_le_halfDiamond _ (hC R).1 (hC R).2).trans hd)
  · exact (csInf_le hbD (Set.mem_range_self R)).trans hd

variable {n K q : ℕ} [Nonempty (Fin K × Fin 1)]

theorem native_low_fault_scalarCrossTerms
    (C : Code n (fun _ => 2) K 1) (d : ℕ) (hdetect : DetectsBelow C d)
    (L : Layers n q) (hq : 1 ≤ q) (W : Operator (Fin K))
    (hW : Implements C (layerSequenceEval L) W)
    (x y : History (fun i : Location L => FaultLabel i))
    (hx : (faults x).card < lowerEnvelope q d L.length)
    (hy : (faults y).card < lowerEnvelope q d L.length) :
    ∃ z : ℂ, (encodedBranch C x).conjTranspose * encodedBranch C y =
      z • (1 : Matrix (Fin K × Fin 1) (Fin K × Fin 1) ℂ) := by
  obtain ⟨hW, Z, hZ, hV⟩ := hW
  have hdual : C.encoding.conjTranspose * layerSequenceEval L =
      (W ⊗ₖ Z) * C.encoding.conjTranspose := by
    have heval := circuitOfLayers_eval L
    rw [← heval] at hV ⊢
    exact point_encoded_dual C (circuitOfLayers L) W Z hW hZ hV
  exact histories_scalarCrossTerm (insertion L) physicalFault physicalFault_supported x y
    chronologicalFaults mem_chronologicalFaults hq d _ (le_max_left _ _) (le_max_right _ _)
    (max_lt hx hy) C hdetect W Z hW hZ hV hdual

/-- The lower envelope gives the coefficient and power for an actual native
circuit with arbitrary correlated local-stochastic Pauli history weights. -/
theorem native_localStochastic_recovery_bounds
    (C : Code n (fun _ => 2) K 1) (d : ℕ) (hdetect : DetectsBelow C d)
    (L : Layers n q) (hq : 1 ≤ q) (W : Operator (Fin K))
    (hW : Implements C (layerSequenceEval L) W) (p : ℝ)
    (μ : LocalStochasticMass (Finset.univ : Finset (Location L))
      (faults (Label := fun i : Location L => FaultLabel i)) p) :
    let bound := ((Fintype.card (Location L)).choose (lowerEnvelope q d L.length) : ℝ) *
      p ^ lowerEnvelope q d L.length
    optimalMassEntanglementInfidelity μ.weight (encodedBranch C) ≤ bound ∧
      optimalMassHalfDiamond μ.weight (encodedBranch C) ≤ bound := by
  simpa only [Finset.card_univ] using
    localStochastic_recovery_bounds Finset.univ faults p μ (encodedBranch C)
      (encodedBranch_isometry C) (lowerEnvelope q d L.length)
      (native_low_fault_scalarCrossTerms C d hdetect L hq W hW)

#print axioms localStochastic_recovery_bounds
#print axioms native_localStochastic_recovery_bounds

end
end CriticalDepth.FaultChannelEffects
