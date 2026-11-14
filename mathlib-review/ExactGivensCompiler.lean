import ExactGivensElimination
import ExactTwoLevelWord
import ConnectedPauliFrameSynthesis
import ExactSerialSynthesis
import SynthesisFiniteWords

/-!
# Full exact Givens synthesis from tensor Pauli rotations

Compile the explicit elimination factors on the computational bitstrings
using Gray routing. The residual phases are singleton control patterns.
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix

noncomputable section

variable {k : ℕ}

private theorem basisPhase_eq_conditionalPhase (x : QubitBasis k) (t : ℝ) :
    conditionalPhase Finset.univ x t =
      diagonal (fun y => if y = x then (Circle.exp t : ℂ) else 1) := by
  unfold conditionalPhase
  congr 1
  funext y
  have h : (∀ i ∈ (Finset.univ : Finset (Fin k)), y i = x i) ↔ y = x :=
    ⟨fun h => funext (fun i => h i (Finset.mem_univ i)), fun h i _ => congrFun h i⟩
  simp only [h]

private theorem diagonal_phase_product (f : QubitBasis k → ℝ) :
    (Finset.univ.noncommProd
      (fun x : QubitBasis k =>
        conditionalPhase Finset.univ x (f x))
      (by
        intro x _ y _ _
        change Commute (conditionalPhase Finset.univ x (f x)) (conditionalPhase Finset.univ y (f y))
        rw [basisPhase_eq_conditionalPhase, basisPhase_eq_conditionalPhase]
        show _ * _ = _ * _
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext z
        exact mul_comm _ _)) =
      diagonal (fun x : QubitBasis k => (Circle.exp (f x) : ℂ)) := by
  classical
  let d (x y : QubitBasis k) := if y = x then (Circle.exp (f x) : ℂ) else 1
  have hx (x : QubitBasis k) : conditionalPhase Finset.univ x (f x) =
      diagonalRingHom (QubitBasis k) ℂ (d x) := basisPhase_eq_conditionalPhase x (f x)
  have hd : ∀ x : QubitBasis k, (∏ y, d y x) = Circle.exp (f x) := by
    intro x
    rw [Finset.prod_eq_single x]
    · simp [d]
    · intro y _ hy
      simp [d, Ne.symm hy]
    · simp
  simp_rw [hx]
  rw [← Finset.map_noncommProd _ _ (fun _ _ _ _ _ => Commute.all _ _),
    Finset.noncommProd_eq_prod]
  apply congrArg Matrix.diagonal
  funext x
  simpa only [Finset.prod_apply] using hd x

private theorem diagonal_mem_pauliWordSubgroup
    (D : Matrix.unitaryGroup (QubitBasis k) ℂ) (d : QubitBasis k → ℂ)
    (hD : D.val = diagonal d) (hd : ∀ x, star (d x) * d x = 1) :
    D ∈ tensorPauliWordSubgroup k := by
  classical
  have hnorm (x : QubitBasis k) : ‖d x‖ = 1 := by
    have h := hd x
    rw [mul_comm, show star (d x) = starRingEnd ℂ (d x) from rfl, Complex.mul_conj'] at h
    apply (sq_eq_sq₀ (norm_nonneg (d x)) (by positivity : (0 : ℝ) ≤ 1)).mp
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re, one_pow]
      using congrArg Complex.re h
  choose f hf using fun x : QubitBasis k => Circle.exp_surjective ⟨d x, mem_sphere_zero_iff_norm.mpr (hnorm x)⟩
  have hfd (x : QubitBasis k) : (Circle.exp (f x) : ℂ) = d x :=
    congrArg (fun z : Circle => (z : ℂ)) (hf x)
  have hEach (x : QubitBasis k) :
      ∃ U : tensorPauliWordSubgroup k, U.val.val = conditionalPhase Finset.univ x (f x) := by
    obtain ⟨L, hL, he⟩ := conditionalPhase_eq_finite_tensorPauliWord Finset.univ x (f x)
    have hw : IsTensorPauliWord L := by
      intro A hA
      obtain ⟨T, _, hT⟩ := hL A hA
      exact ⟨zSubset T, conditionalPauliAngle Finset.univ T x (f x), hT⟩
    exact ⟨⟨L.prod, ⟨L, hw, rfl⟩⟩, he⟩
  choose U hU using hEach
  have hComm : ((Finset.univ : Finset (QubitBasis k)) : Set (QubitBasis k)).Pairwise
      (Function.onFun Commute U) := by
    intro x _ y _ _
    change U x * U y = U y * U x
    apply Subtype.ext
    apply Subtype.ext
    change (U x).val.val * (U y).val.val = (U y).val.val * (U x).val.val
    rw [hU, hU, basisPhase_eq_conditionalPhase, basisPhase_eq_conditionalPhase,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
  let v : tensorPauliWordSubgroup k →* Operator (QubitBasis k) :=
    (Matrix.unitaryGroup (QubitBasis k) ℂ).subtype.comp (tensorPauliWordSubgroup k).subtype
  have hv (x : QubitBasis k) : v (U x) = conditionalPhase Finset.univ x (f x) := hU x
  have hEq : (Finset.univ.noncommProd U hComm).val = D := by
    apply Subtype.ext
    change v (Finset.univ.noncommProd U hComm) = D.val
    rw [Finset.map_noncommProd Finset.univ U hComm v]
    simp_rw [hv]
    rw [diagonal_phase_product f, hD]
    congr 1
    funext x
    exact hfd x
  rw [← hEq]
  exact Subtype.property _

private theorem twoLevel_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (p : RowPair α)
    (A : Operator (Fin 2)) :
    Matrix.reindexAlgEquiv ℂ ℂ e (twoLevel p A) =
      twoLevel (p.trans e.toEmbedding) A := by
  classical
  ext x y
  change twoLevel p A (e.symm x) (e.symm y) = twoLevel (p.trans e.toEmbedding) A x y
  let q := p.trans e.toEmbedding
  have hm (z : β) : z ∈ Set.range q ↔ e.symm z ∈ Set.range p := by
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (e.symm_apply_apply (p i)).symm⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (congrArg e hi).trans (e.apply_symm_apply z)⟩
  have hp (z : α) (hz : z ∉ Set.range p) :
      (rowPairSplit p).symm z = Sum.inr ⟨z, hz⟩ := by
    apply (rowPairSplit p).injective
    exact (rowPairSplit p).apply_symm_apply z
  have hq (z : β) (hz : z ∉ Set.range q) :
      (rowPairSplit q).symm z = Sum.inr ⟨z, hz⟩ := by
    apply (rowPairSplit q).injective
    exact (rowPairSplit q).apply_symm_apply z
  have hinP (i : Fin 2) : (rowPairSplit p).symm (p i) = Sum.inl i :=
    (rowPairSplit p).symm_apply_apply (Sum.inl i)
  have hinQ (i : Fin 2) : (rowPairSplit q).symm (q i) = Sum.inl i :=
    (rowPairSplit q).symm_apply_apply (Sum.inl i)
  have he (i : Fin 2) : e.symm (q i) = p i := e.symm_apply_apply (p i)
  change twoLevel p A (e.symm x) (e.symm y) = twoLevel q A x y
  unfold twoLevel
  change fromBlocks A _ _ _ ((rowPairSplit p).symm (e.symm x))
    ((rowPairSplit p).symm (e.symm y)) =
      fromBlocks A _ _ _ ((rowPairSplit q).symm x) ((rowPairSplit q).symm y)
  by_cases hx : x ∈ Set.range q <;> by_cases hy : y ∈ Set.range q
  · obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    rw [he i, he j, hinP i, hinP j, hinQ i, hinQ j]
    rfl
  · obtain ⟨i, rfl⟩ := hx
    rw [he i, hinP i, hinQ i, hp _ (fun h => hy ((hm y).mpr h)), hq _ hy]
    rfl
  · obtain ⟨j, rfl⟩ := hy
    rw [he j, hinP j, hinQ j, hp _ (fun h => hx ((hm x).mpr h)), hq _ hx]
    rfl
  · rw [hp _ (fun h => hx ((hm x).mpr h)), hp _ (fun h => hy ((hm y).mpr h)),
      hq _ hx, hq _ hy]
    simp [Matrix.fromBlocks, Matrix.one_apply, Subtype.ext_iff, e.symm.injective.eq_iff]

/-- Exact Givens elimination and the Gray/conditional compiler leave no
projective ambiguity in the matrix product. -/
theorem unitary_exists_tensorPauliWord_of_givens
    (e : QubitBasis k ≃ Fin (2 ^ k)) (A : Matrix.unitaryGroup (QubitBasis k) ℂ) :
    ∃ L : TensorPauliWord k, IsTensorPauliWord L ∧ L.prod = A := by
  classical
  let U := unitaryBasisReindex e A
  let L := givensEliminationWord U.val (givensSchedule (2 ^ k))
  obtain ⟨d, hd, hU⟩ := unitary_eq_reverse_givens_with_phases U
  let D : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ := L.prod * U
  have hD : D.val = diagonal d := by
    change L.prod.val * U.val = _
    rw [hU]
    change L.prod.val * ((L.map (·⁻¹)).reverse.prod.val * diagonal d) = _
    rw [← List.prod_inv_reverse, ← Matrix.mul_assoc,
      show L.prod.val * (L.prod⁻¹).val = 1 from L.prod.property.2, Matrix.one_mul]
  let P := unitaryBasisReindex e.symm
  let S := tensorPauliWordSubgroup k
  have hFactors : ∀ V ∈ L, P V ∈ S := by
    intro V hV
    rcases givensEliminationWord_twoLevel_or_identity _ _ V hV with h | ⟨q, B, hB⟩
    · rw [h, map_one]
      exact S.one_mem
    · obtain ⟨M, hM, he⟩ := twoLevel_exists_tensorPauliWord (q.trans e.symm.toEmbedding) B
      refine ⟨M, hM, Subtype.ext ?_⟩
      change M.prod.val = Matrix.reindexAlgEquiv ℂ ℂ e.symm V.val
      rw [hB, twoLevel_reindex, he]
  have hProd : P L.prod ∈ S := by
    rw [← List.prod_hom]
    apply S.list_prod_mem
    intro V hV
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hV
    exact hFactors I hI
  have hD' : (P D).val = diagonal (d ∘ e) := by
    change Matrix.reindexAlgEquiv ℂ ℂ e.symm D.val = _
    rw [hD]
    ext x y
    change diagonal d (e x) (e y) = diagonal (d ∘ e) x y
    simp [Matrix.diagonal_apply, e.injective.eq_iff]
  have hDP : P D ∈ S := diagonal_mem_pauliWordSubgroup _ _ hD' (fun x => hd (e x))
  have hUD : A = (P L.prod)⁻¹ * P D := by
    simp only [D, map_mul, inv_mul_cancel_left]
    apply Subtype.ext
    change A.val = Matrix.reindexAlgEquiv ℂ ℂ e.symm
      (Matrix.reindexAlgEquiv ℂ ℂ e A.val)
    exact ((Matrix.reindexAlgEquiv ℂ ℂ e).symm_apply_apply A.val).symm
  have hA : A ∈ S := hUD ▸ S.mul_mem (S.inv_mem hProd) hDP
  exact hA

#print axioms unitary_exists_tensorPauliWord_of_givens

end

end CriticalDepth.Manuscript20261114
