import FaultStabilizerLogicalBasis

/-!
# Pauli channel optimization on an actual stabilizer code

Each physical Pauli is assigned its realized syndrome, then its relative
logical class modulo scalar phase. The class mass is the sum of the
original physical error masses on that fiber. A CPTP recovery achieves
one minus the sum, across syndromes, of the largest such mass.
-/

namespace CriticalDepth.FaultStabilizerPauliChannel

noncomputable section

open Matrix Module
open CriticalDepth.Manuscript CriticalDepth.PauliGroup
open CriticalDepth.FaultStabilizerSyndrome CriticalDepth.FaultStabilizerLogicalTrace
open CriticalDepth.FaultStabilizerLogicalBasis CriticalDepth.FaultPauliSyndromeChannel
open CriticalDepth.FaultCPTPOptimality CriticalDepth.FaultCPTPRepresentation
open scoped BigOperators

variable {n K : ℕ} [Nonempty (Fin K × Fin 1)]

variable (C : Code n (fun _ => 2) K 1)
variable (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))

abbrev RealizedSyndrome := Set.range (sectorSign S)

instance : Fintype (RealizedSyndrome S) := Fintype.ofFinite _
instance : DecidableEq (RealizedSyndrome S) := Classical.decEq _

local instance : Fintype (PhysPauli n) := Fintype.ofFinite _

def syndromeOf (E : PhysPauli n) : RealizedSyndrome S := ⟨sectorSign S E, E, rfl⟩

def syndromeRepresentative (τ : RealizedSyndrome S) : PhysPauli n := τ.property.choose

private theorem syndromeRepresentative_spec (τ : RealizedSyndrome S) :
    sectorSign S (syndromeRepresentative S τ) = τ.val :=
  τ.property.choose_spec

def encodedError (E : PhysPauli n) : Matrix (QubitBasis n) (Fin K × Fin 1) ℂ :=
  E.val.val * C.encoding

def syndromeIsometry (τ : RealizedSyndrome S) : Matrix (QubitBasis n) (Fin K × Fin 1) ℂ :=
  encodedError C (syndromeRepresentative S τ)

theorem syndromeIsometry_isometric (τ : RealizedSyndrome S) :
    (syndromeIsometry C S τ).conjTranspose * syndromeIsometry C S τ = 1 := by
  let R := (syndromeRepresentative S τ).val.val
  have hu : R.conjTranspose * R = 1 := (syndromeRepresentative S τ).val.property.1
  change (R * C.encoding).conjTranspose * (R * C.encoding) = 1
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R.conjTranspose R,
    hu, Matrix.one_mul, C.isometry]

variable (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})

include hS hspace in
theorem syndromeIsometry_orthogonal (τ σ : RealizedSyndrome S) (hτσ : τ ≠ σ) :
    (syndromeIsometry C S τ).conjTranspose * syndromeIsometry C S σ = 0 := by
  apply syndrome_orthogonal C S hS hspace
  rw [syndromeRepresentative_spec, syndromeRepresentative_spec]
  exact fun h => hτσ (Subtype.ext h)

def relativeLogicalPauli (E : PhysPauli n) : CentralPauli S := by
  let R := syndromeRepresentative S (syndromeOf S E)
  refine ⟨R⁻¹ * E, ?_⟩
  change ∀ T ∈ S, (T : Operator (QubitBasis n)) * (R.val.val.conjTranspose * E.val.val) =
    (R.val.val.conjTranspose * E.val.val) * (T : Operator (QubitBasis n))
  exact same_syndrome_relative_commutes S hS R E (syndromeRepresentative_spec S _)

def logicalClassOf (E : PhysPauli n) : LogicalClass C S :=
  Quotient.mk (logicalPauliSetoid C S) (relativeLogicalPauli S hS E)

include hspace in
private theorem encodedError_eq_syndrome_compress (E : PhysPauli n) :
    encodedError C E = syndromeIsometry C S (syndromeOf S E) *
      compress C (relativeLogicalPauli S hS E).val.val.val := by
  let R := syndromeRepresentative S (syndromeOf S E)
  let P := relativeLogicalPauli S hS E
  have hpres : P.val.val.val * C.encoding = C.encoding * compress C P.val.val.val :=
    code_preservation_of_stabilizer_commutation C S hspace P.val.val.val P.property
  change E.val.val * C.encoding = (R.val.val * C.encoding) * compress C P.val.val.val
  have hP : P.val.val.val = R.val.val.conjTranspose * E.val.val := rfl
  have hu : R.val.val * R.val.val.conjTranspose = 1 := R.val.property.2
  rw [Matrix.mul_assoc, ← hpres, hP, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc R.val.val R.val.val.conjTranspose, hu, Matrix.one_mul]

private theorem phaseBranchLoss {E A : Matrix (QubitBasis n) (Fin K × Fin 1) ℂ}
    (z : ℂ) (hz : star z * z = 1) (he : E = z • A)
    (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) :
    channelBranchLoss E R.val = channelBranchLoss A R.val := by
  have hrecover : recoverBranch R.val E = recoverBranch R.val A := by
    apply LinearMap.ext
    intro X
    change R.val (E * X * E.conjTranspose) = R.val (A * X * A.conjTranspose)
    apply congrArg (fun M => R.val M)
    rw [he, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, hz, one_smul]
  rw [channelBranchLoss, channelBranchLoss, hrecover]

include hspace in
private theorem branchLoss_eq_class (E : PhysPauli n)
    (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) :
    channelBranchLoss (encodedError C E) R.val =
      channelBranchLoss ((syndromeIsometry C S (syndromeOf S E)) *
        logicalMatrix C S (logicalClassOf C S hS E)) R.val := by
  obtain ⟨z, hz, hphase⟩ := chooseLogicalPauli_equivalent C S (relativeLogicalPauli S hS E)
  apply phaseBranchLoss z hz _ R
  rw [encodedError_eq_syndrome_compress C S hS hspace E, hphase, Matrix.mul_smul]
  rfl

/-- The class-indexed probability is obtained by summing probabilities of
the original full physical Pauli sample. -/
def classMass (mass : PhysPauli n → ℝ) (τ : RealizedSyndrome S) (l : LogicalClass C S) : ℝ :=
  ∑ E, if syndromeOf S E = τ ∧ logicalClassOf C S hS E = l then mass E else 0

def physicalPauliChannelLoss (mass : PhysPauli n → ℝ)
    (R : RecoveryChannel (QubitBasis n) (Fin K × Fin 1)) : ℝ :=
  ∑ E, mass E * channelBranchLoss (encodedError C E) R.val

private theorem weighted_class_sum (mass : PhysPauli n → ℝ)
    (f : RealizedSyndrome S → LogicalClass C S → ℝ) :
    (∑ τ, ∑ l, classMass C S hS mass τ l * f τ l) =
      ∑ E, mass E * f (syndromeOf S E) (logicalClassOf C S hS E) := by
  unfold classMass
  simp only [Finset.sum_mul]
  simp_rw [ite_mul, zero_mul]
  rw [show (∑ τ : RealizedSyndrome S, ∑ l : LogicalClass C S,
      ∑ E : PhysPauli n, if syndromeOf S E = τ ∧ logicalClassOf C S hS E = l
        then mass E * f τ l else 0) =
      ∑ τ : RealizedSyndrome S, ∑ E : PhysPauli n,
        ∑ l : LogicalClass C S, if syndromeOf S E = τ ∧ logicalClassOf C S hS E = l
          then mass E * f τ l else 0 from by
      apply Finset.sum_congr rfl
      intro τ _
      exact Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  rw [Finset.sum_eq_single (syndromeOf S E)]
  · simp only [true_and]
    rw [Finset.sum_eq_single (logicalClassOf C S hS E)]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  · intro τ _ hτ
    simp [Ne.symm hτ]
  · simp

private theorem classMass_sum (mass : PhysPauli n → ℝ) (hm : ∑ E, mass E = 1) :
    ∑ τ, ∑ l, classMass C S hS mass τ l = 1 := by
  have h := weighted_class_sum C S hS mass (fun _ _ => 1)
  simp only [mul_one] at h
  exact h.trans hm

include hS hspace in
private theorem dagger_basis :
    ∃ b : Basis (LogicalClass C S) ℂ (Operator (Fin K × Fin 1)),
      TraceOrthogonalUnitaryBasis b ∧ ∀ l, (b l).conjTranspose = logicalMatrix C S l := by
  classical
  let v (l : LogicalClass C S) := (logicalMatrix C S l).conjTranspose
  have htrace (i j : LogicalClass C S) : ((v i).conjTranspose * v j).trace =
      if i = j then (Fintype.card (Fin K × Fin 1) : ℂ) else 0 := by
    simp only [v, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.trace_mul_comm, logicalMatrix_trace C S hS hspace]
    simp only [eq_comm]
  have hlin : LinearIndependent ℂ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro f hf j
    have hz := congrArg (fun M : Operator (Fin K × Fin 1) => ((v j).conjTranspose * M).trace) hf
    simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, htrace, Matrix.mul_zero, Matrix.trace_zero] at hz
    rw [Finset.sum_eq_single j] at hz
    · simp only [ite_true] at hz
      exact (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast Fintype.card_ne_zero)
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  have hSpan : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro M _
    let b := logicalPauliBasis C S hS hspace
    have h := congrArg Matrix.conjTranspose (b.sum_repr M.conjTranspose)
    rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_conjTranspose] at h
    rw [← h]
    apply Submodule.sum_mem
    intro i _
    rw [Matrix.conjTranspose_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i, by simp [b, logicalPauliBasis, Basis.mk_apply, v]⟩
  let b := Basis.mk hlin hSpan
  have hb (l : LogicalClass C S) : b l = v l := Basis.mk_apply _ _ _
  refine ⟨b, ⟨?_, ?_⟩, ?_⟩
  · intro l
    rw [hb]
    exact isUnitary_star (logicalMatrix_unitary C S hspace l)
  · intro i j
    simp only [hb, htrace]
  · intro l
    rw [hb]
    exact Matrix.conjTranspose_conjTranspose _

include hspace in
/-- For the actual stabilizer code and physical Pauli channel, the optimum
over all CPTP maps is one minus the total mass of the chosen most likely
logical class in each realized syndrome. -/
theorem physicalPauliChannelLoss_optimum
    (mass : PhysPauli n → ℝ) (hm : ∑ E, mass E = 1)
    (selected : RealizedSyndrome S → LogicalClass C S)
    (hselected : ∀ τ l, classMass C S hS mass τ l ≤ classMass C S hS mass τ (selected τ)) :
    sInf (Set.range (physicalPauliChannelLoss C mass)) =
      1 - ∑ τ, classMass C S hS mass τ (selected τ) := by
  classical
  obtain ⟨b, hb, hbEq⟩ := dagger_basis C S hS hspace
  have hAs (τ : RealizedSyndrome S) := syndromeIsometry_isometric C S τ
  have hOrth (τ σ : RealizedSyndrome S) (hτσ : τ ≠ σ) :=
    syndromeIsometry_orthogonal C S hS hspace τ σ hτσ
  have hLoss : physicalPauliChannelLoss C mass =
      syndromeChannelLoss (syndromeIsometry C S) b (classMass C S hS mass) := by
    funext R
    unfold physicalPauliChannelLoss syndromeChannelLoss
    simp only [hbEq]
    rw [weighted_class_sum]
    apply Finset.sum_congr rfl
    intro E _
    rw [branchLoss_eq_class C S hS hspace E R]
  rw [hLoss]
  exact syndromeChannelLoss_sInf (syndromeIsometry C S) hAs hOrth b hb
    (classMass C S hS mass) (classMass_sum C S hS mass hm) selected hselected

#print axioms syndromeIsometry_isometric
#print axioms syndromeIsometry_orthogonal
#print axioms physicalPauliChannelLoss_optimum

end
end CriticalDepth.FaultStabilizerPauliChannel
