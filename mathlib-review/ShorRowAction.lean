import ShorNativeLayerAction
import ShorNativeParentLayer
import ShorPermutationAction

/-!
# Computational action of the native Shor layers

The physical matrices are indexed by computational basis words. A binary
linear map acts through the pointwise identification of each qubit bit.
The same identification relates physical Pauli X masks to translations.
-/

open scoped BigOperators Kronecker

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

variable {n q rows columns : ℕ}

/-- Pointwise identification of the physical qubit basis with binary words. -/
def binaryWordEquiv (n : ℕ) : QubitBasis n ≃ (Fin n → Bit) :=
  Equiv.piCongrRight fun _ => qubitBitEquiv

def binaryWordPermutation (e : Equiv.Perm (Fin n → Bit)) :
    Equiv.Perm (QubitBasis n) :=
  ((binaryWordEquiv n).trans e).trans (binaryWordEquiv n).symm

def binaryWordOperator (e : Equiv.Perm (Fin n → Bit)) : Operator (QubitBasis n) :=
  basisPermutation (binaryWordPermutation e)

@[simp] theorem binaryWordOperator_refl :
    binaryWordOperator (Equiv.refl (Fin n → Bit)) = 1 := by
  have h :
      binaryWordPermutation (Equiv.refl (Fin n → Bit)) = Equiv.refl (QubitBasis n) := by
    apply Equiv.ext
    intro x
    exact (binaryWordEquiv n).symm_apply_apply x
  unfold binaryWordOperator
  rw [h]
  ext x y
  rw [basisPermutation_apply, Matrix.one_apply, Equiv.refl_apply]

theorem binaryWordOperator_mul (e f : Equiv.Perm (Fin n → Bit)) :
    binaryWordOperator e * binaryWordOperator f = binaryWordOperator (f.trans e) := by
  unfold binaryWordOperator
  rw [basisPermutation_mul]
  apply congrArg basisPermutation
  apply Equiv.ext
  intro x
  change (binaryWordEquiv n).symm
    (e (binaryWordEquiv n ((binaryWordEquiv n).symm (f (binaryWordEquiv n x))))) =
      (binaryWordEquiv n).symm (e (f (binaryWordEquiv n x)))
  rw [Equiv.apply_symm_apply]

theorem binaryWordOperator_conjTranspose (e : Equiv.Perm (Fin n → Bit)) :
    (binaryWordOperator e).conjTranspose = binaryWordOperator e.symm := by
  unfold binaryWordOperator
  rw [basisPermutation_conjTranspose]
  rfl

/-- Linear computational actions compose in physical execution order. -/
theorem listGateEval_eq_binaryWordOperator
    (gates : List (ListGate n (fun _ => 2) q))
    (T : ListGate n (fun _ => 2) q → (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit))
    (hT : ∀ G ∈ gates, G.gate = binaryWordOperator (T G).toEquiv) :
    listGateEval gates = binaryWordOperator
      (gates.foldl (fun t G => t.trans (T G)) (LinearEquiv.refl Bit (Fin n → Bit))).toEquiv := by
  have h (t : (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit)) :
      listGateEval gates * binaryWordOperator t.toEquiv =
        binaryWordOperator (gates.foldl (fun t G => t.trans (T G)) t).toEquiv := by
    induction gates generalizing t with
    | nil => simp
    | cons G tail ih =>
      rw [listGateEval_cons, Matrix.mul_assoc, hT G (List.mem_cons_self ..),
        binaryWordOperator_mul]
      exact ih (fun H hH => hT H (List.mem_cons_of_mem G hH)) (t.trans (T G))
  have hr : (LinearEquiv.refl Bit (Fin n → Bit)).toEquiv = Equiv.refl (Fin n → Bit) := by
    apply Equiv.ext
    intro x
    rfl
  have he := h (LinearEquiv.refl Bit (Fin n → Bit))
  rwa [hr, binaryWordOperator_refl, Matrix.mul_one] at he

/-- The same execution-order rule for complete lists of padded layers. -/
theorem layerSequenceEval_eq_binaryWordOperator
    (layers : List (Layer n (fun _ => 2) q))
    (T : Layer n (fun _ => 2) q → (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit))
    (hT : ∀ L ∈ layers, L.eval = binaryWordOperator (T L).toEquiv) :
    layerSequenceEval layers = binaryWordOperator
      (layers.foldl (fun t L => t.trans (T L)) (LinearEquiv.refl Bit (Fin n → Bit))).toEquiv := by
  have h (t : (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit)) :
      layerSequenceEval layers * binaryWordOperator t.toEquiv =
        binaryWordOperator (layers.foldl (fun t L => t.trans (T L)) t).toEquiv := by
    induction layers generalizing t with
    | nil => simp [layerSequenceEval]
    | cons L tail ih =>
      rw [layerSequenceEval, Matrix.mul_assoc, hT L (List.mem_cons_self ..),
        binaryWordOperator_mul]
      exact ih (fun K hK => hT K (List.mem_cons_of_mem L hK)) (t.trans (T L))
  have hr : (LinearEquiv.refl Bit (Fin n → Bit)).toEquiv = Equiv.refl (Fin n → Bit) := by
    apply Equiv.ext
    intro x
    rfl
  have he := h (LinearEquiv.refl Bit (Fin n → Bit))
  rwa [hr, binaryWordOperator_refl, Matrix.mul_one] at he

private theorem applyFanoutBlocks_outside (blocks : List (FanoutBlock n q))
    (word : Fin n → Bit) (i : Fin n) (hout : ∀ B ∈ blocks, i ∉ B.sites) :
    blocks.foldl (fun x B => B.run x) word i = word i := by
  induction blocks generalizing word with
  | nil => rfl
  | cons B rest ih =>
    change rest.foldl (fun x T => T.run x) (B.run word) i = word i
    rw [ih (B.run word) (fun T hm => hout T (List.mem_cons_of_mem B hm))]
    exact blockFanout_fixes_outside B.sites B.pivot word i (hout B (by simp))

private theorem activeParentBlock_mem (parent : Fin n → Option (Fin n))
    (hcard : ∀ a, (parentSites parent a).card ≤ q)
    (a : Fin n) (ha : (targetSites parent a).Nonempty) :
    (⟨parentSites parent a, ⟨a, (parentSites_mem parent a a).mpr (.inl rfl)⟩, hcard a⟩ :
      FanoutBlock n q) ∈ parentBlocks parent hcard := by
  classical
  unfold parentBlocks
  apply List.mem_map.mpr
  exact ⟨a, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩), rfl⟩

/-- The simultaneous disjoint parent blocks implement exactly the parent map. -/
theorem parentBlocks_run (parent : Fin n → Option (Fin n))
    (huntouched : ∀ i a, parent i = some a → parent a = none)
    (hcard : ∀ a, (parentSites parent a).card ≤ q)
    (word : Fin n → Bit) :
    (parentBlocks parent hcard).foldl (fun x B => B.run x) word = fanout parent word := by
  classical
  funext i
  cases hi : parent i with
  | none =>
    by_cases hactive : (targetSites parent i).Nonempty
    · let B : FanoutBlock n q :=
        ⟨parentSites parent i, ⟨i, (parentSites_mem parent i i).mpr (.inl rfl)⟩, hcard i⟩
      rw [applyBlocks_on_block _ (parentBlocks_pairwise parent huntouched hcard) word B
        (activeParentBlock_mem parent hcard i hactive) i ((parentSites_mem parent i i).mpr (.inl rfl))]
      change blockFanoutEquiv (parentSites parent i) i word i = fanout parent word i
      simp [blockFanoutEquiv_apply, fanout, hi]
    · rw [applyFanoutBlocks_outside]
      · simp [fanout, hi]
      · intro B hB
        unfold parentBlocks at hB
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hB
        have ha' : (targetSites parent a).Nonempty := (Finset.mem_filter.mp
          (Finset.mem_toList.mp ha)).2
        intro hsite
        rcases (parentSites_mem parent i a).mp hsite with rfl | heq
        · exact hactive ha'
        · simp [hi] at heq
  | some a =>
    have ha : (targetSites parent a).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hia : i ≠ a := by
      intro heq
      subst a
      rw [huntouched i i hi] at hi
      cases hi
    let B : FanoutBlock n q :=
      ⟨parentSites parent a, ⟨a, (parentSites_mem parent a a).mpr (.inl rfl)⟩, hcard a⟩
    have hs := (parentSites_mem parent i a).mpr (.inr hi)
    rw [applyBlocks_on_block _ (parentBlocks_pairwise parent huntouched hcard) word B
      (activeParentBlock_mem parent hcard a ha) i hs]
    change blockFanoutEquiv (parentSites parent a) a word i = fanout parent word i
    simp [blockFanoutEquiv_apply, hs, hia, fanout, hi]

private theorem basisPermutation_mulVec_single {β : Type*} [Fintype β] [DecidableEq β]
    (e : Equiv.Perm β) (x : β) :
    (basisPermutation e).mulVec (Pi.single x (1 : ℂ)) = Pi.single (e x) 1 := by
  rw [Matrix.mulVec_single_one]
  funext y
  change basisPermutation e y x = (Pi.single (e x) (1 : ℂ) : β → ℂ) y
  simp [basisPermutation_apply, Pi.single_apply]

/-- Exact physical matrix of a bounded simultaneous parent map. -/
theorem nativeParentLayer_eval (parent : Fin n → Option (Fin n))
    (huntouched : ∀ i a, parent i = some a → parent a = none)
    (hcard : ∀ a, (parentSites parent a).card ≤ q) :
    (nativeParentLayer parent huntouched hcard).eval =
      binaryWordOperator (fanoutLinearEquiv parent huntouched).toEquiv := by
  classical
  ext x y
  let w := binaryWordEquiv n y
  have h := fanoutLayerOfBlocks_eval_basis
    (parentBlocks parent hcard) (parentBlocks_pairwise parent huntouched hcard) w
  change (nativeParentLayer parent huntouched hcard).eval.mulVec
      (Pi.single ((binaryWordEquiv n).symm w) (1 : ℂ)) =
    Pi.single ((binaryWordEquiv n).symm
      ((parentBlocks parent hcard).foldl (fun z B => B.run z) w)) 1 at h
  rw [parentBlocks_run parent huntouched hcard, show (binaryWordEquiv n).symm w = y by
    exact (binaryWordEquiv n).symm_apply_apply y] at h
  have hr := basisPermutation_mulVec_single
    (binaryWordPermutation (fanoutLinearEquiv parent huntouched).toEquiv) y
  change (binaryWordOperator (fanoutLinearEquiv parent huntouched).toEquiv).mulVec
      (Pi.single y 1) =
    Pi.single ((binaryWordEquiv n).symm (fanout parent w)) 1 at hr
  rw [Matrix.mulVec_single_one] at h hr
  exact congrFun (h.trans hr.symm) x

/-- Reindex a linear qubit word as a rectangular binary mask. -/
def shorWordLinearEquiv (rows columns : ℕ) :
    (Fin (rows * columns) → Bit) ≃ₗ[Bit] Mask rows columns :=
  LinearEquiv.funCongrLeft Bit Bit (shorSiteEquiv rows columns).symm

/-- The binary-word form of the same row transformation in every column. -/
def acrossColumnsPhysicalLinearEquiv (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) :
    (Fin (rows * columns) → Bit) ≃ₗ[Bit] (Fin (rows * columns) → Bit) :=
  ((shorWordLinearEquiv rows columns).trans (acrossColumnsLinearEquiv T)).trans
    (shorWordLinearEquiv rows columns).symm

private theorem binaryWordPermutation_acrossColumns
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) :
    binaryWordPermutation (acrossColumnsPhysicalLinearEquiv (columns := columns) T).toEquiv =
      (((shorBasisEquiv rows columns).trans (acrossColumnsLinearEquiv T).toEquiv).trans
        (shorBasisEquiv rows columns).symm) := by
  apply Equiv.ext
  intro x
  funext i
  rfl

/-- A row transformation fixing the all-ones word acts as the identity
on the physical Shor encoding when used in every column. -/
theorem binaryWordOperator_acrossColumns_fixes_physicalShorEncoding
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) (hT : T 1 = 1) :
    binaryWordOperator (acrossColumnsPhysicalLinearEquiv (columns := columns + 1) T).toEquiv *
      physicalShorEncoding rows columns = physicalShorEncoding rows columns := by
  classical
  let E := shorBasisEquiv rows (columns + 1)
  let P := (acrossColumnsLinearEquiv (columns := columns + 1) T).toEquiv
  have hp := acrossColumnsPermutation_fixes_shorEncoding (columns := columns) T hT
  ext x b
  unfold binaryWordOperator
  rw [binaryWordPermutation_acrossColumns, basisPermutation_mul_apply]
  change shorEncoding rows columns (E (E.symm (P.symm (E x)))) (shorLogicalEquiv b) =
    shorEncoding rows columns (E x) (shorLogicalEquiv b)
  rw [Equiv.apply_symm_apply]
  have h := congrArg (fun M => M (E x) (shorLogicalEquiv b)) hp
  rwa [show (basisPermutation P * shorEncoding rows columns) (E x) (shorLogicalEquiv b) =
    shorEncoding rows columns (P.symm (E x)) (shorLogicalEquiv b) from
    basisPermutation_mul_apply P _ _ _] at h

/-- The physical Shor code sees the columnwise row map as logical identity. -/
theorem physicalShorCode_implements_one_of_acrossColumns
    (r : Fin rows) (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) (hT : T 1 = 1)
    (U : Operator (QubitBasis (rows * (columns + 1))))
    (hEval : U = binaryWordOperator
      (acrossColumnsPhysicalLinearEquiv (columns := columns + 1) T).toEquiv) :
    Implements (physicalShorCode (columns := columns) r) U 1 := by
  refine ⟨isUnitary_one, 1, isUnitary_one, ?_⟩
  rw [Matrix.one_kronecker_one, Matrix.mul_one, hEval]
  exact binaryWordOperator_acrossColumns_fixes_physicalShorEncoding T hT

/-- A physical tensor X acts as binary translation of the matching mask. -/
theorem physicalXWord_eq_binaryWordOperator_translate (a : Mask rows columns) :
    pauliMatrix 0 (physicalXWord a) =
      binaryWordOperator (translate ((shorWordLinearEquiv rows columns).symm a)) := by
  classical
  let E := shorBasisEquiv rows columns
  let A := (shorWordLinearEquiv rows columns).symm a
  have hperm : binaryWordPermutation (translate A) =
      (E.trans (translate a)).trans E.symm := by
    apply Equiv.ext
    intro x
    funext i
    change qubitBitEquiv.symm
      (qubitBitEquiv (x i) + a (shorSiteEquiv rows columns i)) =
        qubitBitEquiv.symm
          (qubitBitEquiv (x ((shorSiteEquiv rows columns).symm
            (shorSiteEquiv rows columns i))) + a (shorSiteEquiv rows columns i))
    rw [Equiv.symm_apply_apply]
  ext x y
  have heq : (Pi.single (E y) (1 : ℂ)) ∘ E = Pi.single y 1 := by
    funext z
    simp [Pi.single_apply]
  have h := physicalXWord_mulVec a (Pi.single (E y) 1) x
  rw [heq, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  change _ = basisPermutation (binaryWordPermutation (translate A)) x y
  change pauliMatrix 0 (physicalXWord a) x y =
    basisPermutation (translate a) (E x) (E y) at h
  rw [basisPermutation_apply] at h
  rw [hperm, basisPermutation_apply]
  have hiff :
      E x = translate a (E y) ↔ x = ((E.trans (translate a)).trans E.symm) y := by
    change E x = translate a (E y) ↔ x = E.symm (translate a (E y))
    exact E.eq_symm_apply.symm
  split
  · rename_i hx
    rw [ite_eq_left (hiff.mpr hx)] at h
    exact h
  · rename_i hx
    rw [ite_eq_right (fun hEq => hx (hiff.mp hEq))] at h
    exact h

theorem binaryWordOperator_conjugates_translate
    (T : (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit)) (a : Fin n → Bit) :
    binaryWordOperator T.toEquiv * binaryWordOperator (translate a) *
      (binaryWordOperator T.toEquiv).conjTranspose =
        binaryWordOperator (translate (T a)) := by
  rw [binaryWordOperator_conjTranspose, binaryWordOperator_mul, binaryWordOperator_mul]
  apply congrArg binaryWordOperator
  apply Equiv.ext
  intro x
  change T (T.symm x + a) = x + T a
  rw [map_add, LinearEquiv.apply_symm_apply]

/-- Conjugating a physical X mask applies the binary transformation to its mask. -/
theorem binaryWordOperator_conjugates_physicalXWord
    (T : (Fin (rows * columns) → Bit) ≃ₗ[Bit] (Fin (rows * columns) → Bit))
    (a : Mask rows columns) :
    binaryWordOperator T.toEquiv * pauliMatrix 0 (physicalXWord a) *
      (binaryWordOperator T.toEquiv).conjTranspose =
        pauliMatrix 0 (physicalXWord
          (shorWordLinearEquiv rows columns (T ((shorWordLinearEquiv rows columns).symm a)))) := by
  rw [physicalXWord_eq_binaryWordOperator_translate, binaryWordOperator_conjugates_translate,
    physicalXWord_eq_binaryWordOperator_translate, LinearEquiv.symm_apply_apply]

#print axioms listGateEval_eq_binaryWordOperator
#print axioms layerSequenceEval_eq_binaryWordOperator
#print axioms nativeParentLayer_eval
#print axioms binaryWordOperator_acrossColumns_fixes_physicalShorEncoding
#print axioms physicalShorCode_implements_one_of_acrossColumns
#print axioms binaryWordOperator_conjugates_physicalXWord

end CriticalDepth.FaultShorSaturation
