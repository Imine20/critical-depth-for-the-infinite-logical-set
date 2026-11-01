import CriticalDepth.FieldLayerDerivative

/-!
# Distance detection of the actual two-sided circuit insertions

Every term is obtained from the finite derivative expansion of the real gate
products. The short-cone hypothesis is a numerical bound to be discharged by
the manuscript depth inequality, rather than an assumed generator identity.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

variable {F : Type*} [Field F] [Algebra ℂ F]
variable {n q ℓ g d : ℕ} {dim : Fin n → ℕ}

theorem fieldLayerSequenceEval_append
    (before after : List (FieldLayer (K := F) n dim q)) :
    fieldLayerSequenceEval (before ++ after) =
      fieldLayerSequenceEval after * fieldLayerSequenceEval before := by
  induction before with
  | nil => simp [fieldLayerSequenceEval]
  | cons L before ih =>
      simp only [List.cons_append, fieldLayerSequenceEval, ih, Matrix.mul_assoc]

theorem fieldLayerSequenceInv_append
    (before after : List (FieldLayer (K := F) n dim q)) :
    fieldLayerSequenceInv (before ++ after) =
      fieldLayerSequenceInv before * fieldLayerSequenceInv after := by
  induction before with
  | nil => simp [fieldLayerSequenceInv]
  | cons L before ih =>
      simp only [List.cons_append, fieldLayerSequenceInv, ih, Matrix.mul_assoc]

theorem layerGateInsertionAt_exists_split (D : Derivation ℂ F F)
    (layers : List (FieldLayer (K := F) n dim q))
    (r : Fin layers.length) (j : Fin n) :
    ∃ (before : List (FieldLayer (K := F) n dim q))
      (L : FieldLayer (K := F) n dim q)
      (after : List (FieldLayer (K := F) n dim q)),
      layers = before ++ L :: after ∧
      layerGateInsertionAt D layers r j =
        fieldLayerSequenceEval after *
          (matrixDerivation D (L.gate j).1 * (L.gate j).2) *
            fieldLayerSequenceInv after := by
  revert r
  induction layers with
  | nil => intro r; exact Fin.elim0 r
  | cons L layers ih =>
      intro r
      refine Fin.cases ?_ (fun t => ?_) r
      · exact ⟨[], L, layers, rfl, rfl⟩
      · obtain ⟨before, M, after, heq, hins⟩ := ih t
        refine ⟨L :: before, M, after, ?_, ?_⟩
        · simpa only [List.cons_append] using congrArg (List.cons L) heq
        · exact hins

theorem blockInsertion_mem_gaugeOnly
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hq : 1 ≤ q)
    (D : Derivation ℂ F F)
    (before : List (FieldLayer (K := F) n dim q))
    (L : FieldLayer (K := F) n dim q)
    (after : List (FieldLayer (K := F) n dim q)) (j : Fin n)
    (W Wi : Matrix (Fin ℓ) (Fin ℓ) F) (Z Zi : Matrix (Fin g) (Fin g) F)
    (hW : W * Wi = 1 ∧ Wi * W = 1) (hZ : Z * Zi = 1 ∧ Zi * Z = 1)
    (hencoded : fieldLayerSequenceEval (before ++ L :: after) *
      C.encoding.map (algebraMap ℂ F) =
      C.encoding.map (algebraMap ℂ F) * (W ⊗ₖ Z))
    (hdual : C.encoding.conjTranspose.map (algebraMap ℂ F) *
      fieldLayerSequenceEval (before ++ L :: after) =
      (W ⊗ₖ Z) * C.encoding.conjTranspose.map (algebraMap ℂ F))
    (hshort : q ^ (after.length + 1) < d ∨ q ^ (before.length + 1) < d) :
    fieldLayerSequenceEval after *
      (matrixDerivation D (L.gate j).1 * (L.gate j).2) *
        fieldLayerSequenceInv after ∈ gaugeOnlySubmodule (K := F) C := by
  let S := L.layout.support j
  let O := matrixDerivation D (L.gate j).1 * (L.gate j).2
  let H := fieldLayerSequenceEval after * O * fieldLayerSequenceInv after
  change H ∈ gaugeOnlySubmodule (K := F) C
  rcases hshort with hforward | hbackward
  · have hcard : (fieldLayerSequenceCone after S).card < d := by
      calc
        (fieldLayerSequenceCone after S).card ≤ q ^ after.length * S.card :=
          fieldLayerSequenceCone_card_le after S hq
        _ ≤ q ^ after.length * q := Nat.mul_le_mul_left _ (L.layout.arity j)
        _ = q ^ (after.length + 1) := (pow_succ q after.length).symm
        _ < d := hforward
    exact supportedSpan_le_gaugeOnlySubmodule C hDetect _ hcard
      (fieldLayerSequence_conjugate_mem after S (L.logarithmic_gate_mem D j))
  · have hcard : (fieldLayerSequenceBackwardCone before S).card < d := by
      calc
        (fieldLayerSequenceBackwardCone before S).card ≤ q ^ before.length * S.card :=
          fieldLayerSequenceBackwardCone_card_le before S hq
        _ ≤ q ^ before.length * q := Nat.mul_le_mul_left _ (L.layout.arity j)
        _ = q ^ (before.length + 1) := (pow_succ q before.length).symm
        _ < d := hbackward
    have hlocal : L.evalInv * O * L.eval ∈ supportedSpan (K := F) S :=
      L.backward_conjugated_logarithmic_gate_mem D j
    have hb : fieldLayerSequenceInv before * (L.evalInv * O * L.eval) *
        fieldLayerSequenceEval before ∈ gaugeOnlySubmodule (K := F) C :=
      supportedSpan_le_gaugeOnlySubmodule C hDetect _ hcard
        (fieldLayerSequence_inverse_conjugate_mem before S hlocal)
    obtain ⟨N, hN⟩ := hb
    let E := C.encoding.conjTranspose.map (algebraMap ℂ F)
    let V := C.encoding.map (algebraMap ℂ F)
    let U := fieldLayerSequenceEval (before ++ L :: after)
    let Ui := fieldLayerSequenceInv (before ++ L :: after)
    have ha := fieldLayerSequence_mutual_inverse after
    have hu := fieldLayerSequence_mutual_inverse (before ++ L :: after)
    have hframe : E * Ui * H * U * V = (1 : Matrix (Fin ℓ) (Fin ℓ) F) ⊗ₖ N := by
      calc
        E * Ui * H * U * V =
            E * (fieldLayerSequenceInv before * L.evalInv *
              (fieldLayerSequenceInv after * fieldLayerSequenceEval after) * O *
              (fieldLayerSequenceInv after * fieldLayerSequenceEval after) *
              L.eval * fieldLayerSequenceEval before) * V := by
          simp only [U, Ui, H, fieldLayerSequenceEval_append, fieldLayerSequenceInv_append,
            fieldLayerSequenceEval, fieldLayerSequenceInv, Matrix.mul_assoc]
        _ = E * fieldLayerSequenceInv before * (L.evalInv * O * L.eval) *
            fieldLayerSequenceEval before * V := by
          rw [ha.2]
          simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
        _ = (1 : Matrix (Fin ℓ) (Fin ℓ) F) ⊗ₖ N := by
          simpa only [E, V, Matrix.mul_assoc] using hN
    refine ⟨Z * N * Zi, ?_⟩
    exact algebraic_gauge_frame_transfer E V U Ui H W Wi Z Zi N
      hu.1 hu.2 hW.1 hW.2 hZ.1 hZ.2 hencoded hdual hframe

theorem fieldLayerSequence_derivative_mem_gaugeOnly
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hq : 1 ≤ q)
    (D : Derivation ℂ F F) (layers : List (FieldLayer (K := F) n dim q))
    (W Wi : Matrix (Fin ℓ) (Fin ℓ) F) (Z Zi : Matrix (Fin g) (Fin g) F)
    (hW : W * Wi = 1 ∧ Wi * W = 1) (hZ : Z * Zi = 1 ∧ Zi * Z = 1)
    (hencoded : fieldLayerSequenceEval layers * C.encoding.map (algebraMap ℂ F) =
      C.encoding.map (algebraMap ℂ F) * (W ⊗ₖ Z))
    (hdual : C.encoding.conjTranspose.map (algebraMap ℂ F) * fieldLayerSequenceEval layers =
      (W ⊗ₖ Z) * C.encoding.conjTranspose.map (algebraMap ℂ F))
    (hshort : ∀ before L after, layers = before ++ L :: after →
      q ^ (after.length + 1) < d ∨ q ^ (before.length + 1) < d) :
    matrixDerivation D (fieldLayerSequenceEval layers) * fieldLayerSequenceInv layers ∈
      gaugeOnlySubmodule (K := F) C := by
  rw [fieldLayerSequence_logarithmic_derivative_eq_sum]
  apply (gaugeOnlySubmodule (K := F) C).sum_mem
  intro r _
  apply (gaugeOnlySubmodule (K := F) C).sum_mem
  intro j _
  obtain ⟨before, L, after, heq, hins⟩ := layerGateInsertionAt_exists_split D layers r j
  rw [hins]
  apply blockInsertion_mem_gaugeOnly C hDetect hq D before L after j W Wi Z Zi hW hZ
  · simpa only [heq] using hencoded
  · simpa only [heq] using hdual
  · exact hshort before L after heq

end CriticalDepth.Manuscript
