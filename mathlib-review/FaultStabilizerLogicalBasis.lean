import FaultStabilizerLogicalTrace
import FaultPauliSyndromeChannel

/-!
# Complete trace-orthogonal logical Pauli classes

A finite quotient chooses one unitary for each scalar-equivalence class
of compressed centralizing physical Pauli operators. The trace criterion
gives linear independence and the compression spanning result gives
completeness on the actual logical carrier.
-/

namespace CriticalDepth.FaultStabilizerLogicalBasis

noncomputable section

open Matrix Module
open CriticalDepth.Manuscript CriticalDepth.PauliGroup
open CriticalDepth.FaultStabilizerLogicalTrace CriticalDepth.FaultStabilizerSyndrome
open CriticalDepth.FaultPauliSyndromeChannel
open scoped BigOperators

variable {n K : ℕ} [Nonempty (Fin K × Fin 1)]
variable (C : Code n (fun _ => 2) K 1)
variable (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))

private abbrev Commutes (P : Operator (QubitBasis n)) :=
  ∀ T ∈ S, (T : Operator (QubitBasis n)) * P = P * (T : Operator (QubitBasis n))

abbrev CentralPauli := {E : PhysPauli n // Commutes S E.val.val}

theorem centralPauli_compress_isUnitary (P : CentralPauli S)
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v}) :
    IsUnitary (compress C P.val.val.val) := by
  let R := P.val.val.val
  let A := compress C R
  have hp : R * C.encoding = C.encoding * A :=
    code_preservation_of_stabilizer_commutation C S hspace R P.property
  have hR : R.conjTranspose * R = 1 := P.val.val.property.1
  have hu : (C.encoding * A).conjTranspose * (C.encoding * A) = 1 := by
    rw [← hp, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc R.conjTranspose R, hR, Matrix.one_mul, C.isometry]
  have hA : A.conjTranspose * A = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc C.encoding.conjTranspose C.encoding A,
      C.isometry, Matrix.one_mul] using hu
  exact ⟨hA, (mul_eq_one_comm).mp hA⟩

private theorem compress_relative (P Q : CentralPauli S)
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v}) :
    (compress C P.val.val.val).conjTranspose * compress C Q.val.val.val =
      compress C (P.val.val.val.conjTranspose * Q.val.val.val) := by
  let U : Operator (QubitBasis n) := P.val.val.val
  let V : Operator (QubitBasis n) := Q.val.val.val
  have hu : U * C.encoding = C.encoding * compress C U :=
    code_preservation_of_stabilizer_commutation C S hspace U P.property
  have hv : V * C.encoding = C.encoding * compress C V :=
    code_preservation_of_stabilizer_commutation C S hspace V Q.property
  change (compress C U).conjTranspose * compress C V = compress C (U.conjTranspose * V)
  calc
    _ = (C.encoding * compress C U).conjTranspose * (C.encoding * compress C V) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc C.encoding.conjTranspose C.encoding, C.isometry, Matrix.one_mul]
    _ = _ := by rw [← hu, ← hv]; simp [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]

def logicalPauliSetoid : Setoid (CentralPauli S) where
  r a b := ProjectivelyEquivalent (compress C a.val.val.val) (compress C b.val.val.val)
  iseqv := ⟨fun a => projectivelyEquivalent_refl _, fun h => projectivelyEquivalent_symm h,
    fun ha hb => projectivelyEquivalent_trans ha hb⟩

abbrev LogicalClass := Quotient (logicalPauliSetoid C S)

instance : Finite (PhysPauli n) := by
  classical
  have h : ({A : Operator (QubitBasis n) | IsPauli A} : Set (Operator (QubitBasis n))).Finite :=
    ReviewV2.pauliOperator_set_finite n
  letI : Fintype {A : Operator (QubitBasis n) // IsPauli A} := h.fintype
  apply Finite.of_injective (fun p : PhysPauli n =>
    (⟨p.val.val, p.property⟩ : {A : Operator (QubitBasis n) // IsPauli A}))
  intro x y hxy
  have hval : x.val.val = y.val.val :=
    congrArg (fun p : {A : Operator (QubitBasis n) // IsPauli A} => p.val) hxy
  exact Subtype.ext (Subtype.ext hval)

instance : Nonempty (CentralPauli S) :=
  ⟨⟨1, fun T _ => by change T.val * 1 = 1 * T.val; simp⟩⟩

instance : Fintype (LogicalClass C S) := Fintype.ofFinite _

instance : DecidableEq (LogicalClass C S) := Classical.decEq _

def chooseLogicalPauli (c : LogicalClass C S) : CentralPauli S :=
  Classical.choose (Quotient.mk_surjective c)

private theorem chooseLogicalPauli_spec (c : LogicalClass C S) :
    Quotient.mk (logicalPauliSetoid C S) (chooseLogicalPauli C S c) = c :=
  Classical.choose_spec (Quotient.mk_surjective c)

def logicalMatrix (c : LogicalClass C S) : Operator (Fin K × Fin 1) :=
  compress C (chooseLogicalPauli C S c).val.val.val

theorem chooseLogicalPauli_equivalent (P : CentralPauli S) :
    ProjectivelyEquivalent (compress C P.val.val.val)
      (logicalMatrix C S (Quotient.mk (logicalPauliSetoid C S) P)) := by
  change (logicalPauliSetoid C S).r P (chooseLogicalPauli C S (Quotient.mk (logicalPauliSetoid C S) P))
  exact Quotient.exact (chooseLogicalPauli_spec C S _).symm

variable (hS : ∀ T ∈ S, IsPauli (T : Operator (QubitBasis n)))
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})

include hspace in
theorem logicalMatrix_unitary (c : LogicalClass C S) : IsUnitary (logicalMatrix C S c) :=
  centralPauli_compress_isUnitary C S (chooseLogicalPauli C S c) hspace

private theorem relative_scalar_gives_phase
    (U V : Operator (Fin K × Fin 1)) (hU : IsUnitary U) (hV : IsUnitary V)
    (h : IsScalar (U.conjTranspose * V)) : ProjectivelyEquivalent V U := by
  obtain ⟨z, hz⟩ := h
  have hv : V = z • U := by
    have hh := congrArg (fun M => U * M) hz
    simpa only [← Matrix.mul_assoc, show U * U.conjTranspose = 1 from hU.2,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] using hh
  have hs : (star z * z) • (1 : Operator (Fin K × Fin 1)) = 1 := by
    have ht : V.conjTranspose * V = 1 := hV.1
    rwa [hv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, show U.conjTranspose * U = 1 from hU.1] at ht
  let i := Classical.choice (inferInstance : Nonempty (Fin K × Fin 1))
  refine ⟨z, ?_, hv⟩
  have ht := congrArg (fun M : Operator (Fin K × Fin 1) => M i i) hs
  simpa [Matrix.smul_apply, smul_eq_mul] using ht

include hS hspace in
theorem logicalMatrix_trace (a b : LogicalClass C S) :
    ((logicalMatrix C S a).conjTranspose * logicalMatrix C S b).trace =
      if a = b then (Fintype.card (Fin K × Fin 1) : ℂ) else 0 := by
  by_cases hab : a = b
  · subst b
    have hu : (logicalMatrix C S a).conjTranspose * logicalMatrix C S a = 1 :=
      (logicalMatrix_unitary C S hspace a).1
    rw [hu, Matrix.trace_one, if_pos rfl]
  · rw [ite_eq_right hab]
    let P := chooseLogicalPauli C S a
    let Q := chooseLogicalPauli C S b
    change ((compress C P.val.val.val).conjTranspose * compress C Q.val.val.val).trace = 0
    rw [compress_relative C S P Q hspace]
    apply compress_trace_zero_unless_scalar C S hS hspace
    · exact isPauli_mul (isPauli_star P.val.property) Q.val.property
    · intro hs
      rw [← compress_relative C S P Q hspace] at hs
      have hq := relative_scalar_gives_phase _ _ (logicalMatrix_unitary C S hspace a)
        (logicalMatrix_unitary C S hspace b) hs
      have he : Quotient.mk (logicalPauliSetoid C S) P = Quotient.mk (logicalPauliSetoid C S) Q :=
        Quotient.sound (projectivelyEquivalent_symm hq)
      exact hab ((chooseLogicalPauli_spec C S a).symm.trans
        (he.trans (chooseLogicalPauli_spec C S b)))

private theorem logicalMatrix_linearIndependent (htrace : ∀ a b,
    ((logicalMatrix C S a).conjTranspose * logicalMatrix C S b).trace =
      if a = b then (Fintype.card (Fin K × Fin 1) : ℂ) else 0) :
    LinearIndependent ℂ (logicalMatrix C S) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f hf j
  have hz := congrArg (fun M : Operator (Fin K × Fin 1) =>
    ((logicalMatrix C S j).conjTranspose * M).trace) hf
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, htrace, Matrix.mul_zero, Matrix.trace_zero] at hz
  rw [Finset.sum_eq_single j] at hz
  · simp only [ite_true] at hz
    exact (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast Fintype.card_ne_zero)
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

include hS hspace in
private theorem logicalMatrix_spans :
    ⊤ ≤ Submodule.span ℂ (Set.range (logicalMatrix C S)) := by
  rw [← compressed_centralizingPaulis_span C S hS hspace]
  apply Submodule.span_le.mpr
  rintro A ⟨P, hP, hcomm, rfl⟩
  let U : Matrix.unitaryGroup (QubitBasis n) ℂ := ⟨P, by
    obtain ⟨a, p, rfl⟩ := hP
    exact pauliMatrix_isUnitary a p⟩
  let x : CentralPauli S := ⟨⟨U, hP⟩, hcomm⟩
  obtain ⟨z, _, hz⟩ := chooseLogicalPauli_equivalent C S x
  rw [show compress C P = _ from hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

/-- All projective logical Pauli classes have a trace-orthogonal
representative basis of the entire encoded matrix space. -/
def logicalPauliBasis : Basis (LogicalClass C S) ℂ (Operator (Fin K × Fin 1)) :=
  Basis.mk (logicalMatrix_linearIndependent C S (logicalMatrix_trace C S hS hspace))
    (logicalMatrix_spans C S hS hspace)

theorem logicalPauliBasis_is_traceOrthogonal :
    TraceOrthogonalUnitaryBasis (logicalPauliBasis C S hS hspace) := by
  classical
  unfold logicalPauliBasis
  exact ⟨by simpa only [Basis.mk_apply] using logicalMatrix_unitary C S hspace,
    by simpa only [Basis.mk_apply] using logicalMatrix_trace C S hS hspace⟩

#print axioms centralPauli_compress_isUnitary
#print axioms logicalPauliBasis_is_traceOrthogonal

end
end CriticalDepth.FaultStabilizerLogicalBasis
