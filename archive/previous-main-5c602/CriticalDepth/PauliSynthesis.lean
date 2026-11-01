import CriticalDepth.PauliCompression
import CriticalDepth.LayerOperations

/-!
# Iterated compression and actual critical-depth Pauli-rotation circuits

All layers act on the same n physical qubits. The synthesis consists of
compression, one supported middle gate, and the reverse adjoint compression
sequence. List-to-circuit packing preserves the actual evaluated matrix.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {n q : ℕ} {dim : Fin n → ℕ}

def circuitOfLayers (layers : List (Layer n dim q)) : Circuit n dim q layers.length :=
  fun i => layers[i.val]

theorem circuitOfLayers_list (layers : List (Layer n dim q)) :
    List.ofFn (circuitOfLayers layers) = layers := by
  exact List.ofFn_getElem

theorem circuitOfLayers_eval (layers : List (Layer n dim q)) :
    circuitEval (circuitOfLayers layers) = layerSequenceEval layers := by
  have hm' : List.ofFn (fun i => (circuitOfLayers layers i).eval) =
      layers.map Layer.eval := by
    exact List.ofFn_getElem_eq_map layers Layer.eval
  unfold circuitEval
  rw [hm']
  exact (layerSequenceEval_eq_reverse_prod layers).symm

theorem circuitEval_cast {h h' : ℕ} (e : h = h') (c : Circuit n dim q h) :
    circuitEval (e ▸ c : Circuit n dim q h') = circuitEval c := by
  cases e
  rfl

theorem compressedWeight_shift (q w r : ℕ) :
    Arithmetic.compressedWeight q (Arithmetic.ceilDiv w q) r =
      Arithmetic.compressedWeight q w (r + 1) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Arithmetic.compressedWeight, ih]

/-- Iteration realizes the exact arithmetic support recurrence on the original register. -/
theorem pauli_compression_sequence (q : ℕ) (hq : 1 ≤ q)
    (p : Fin n → SinglePauli) (r : ℕ) :
    ∃ layers : List (Layer n (fun _ => 2) q), ∃ p' : Fin n → SinglePauli,
      layers.length = r ∧
      layerSequenceEval layers * pauliMatrix (0 : Fin 4) p * star (layerSequenceEval layers) =
        pauliMatrix (0 : Fin 4) p' ∧
      (pauliSupport p').card = Arithmetic.compressedWeight q (pauliSupport p).card r := by
  classical
  induction r generalizing p with
  | zero =>
      refine ⟨[], p, rfl, ?_, rfl⟩
      simp [layerSequenceEval]
  | succ r ih =>
      obtain ⟨p₁, L, hL, hwL⟩ := pauli_compression_layer q hq p
      obtain ⟨layers, p', hlen, hconj, hweight⟩ := ih p₁
      refine ⟨L :: layers, p', by simp [hlen], ?_, ?_⟩
      · calc
          layerSequenceEval (L :: layers) * pauliMatrix (0 : Fin 4) p *
              star (layerSequenceEval (L :: layers)) =
            layerSequenceEval layers *
              (L.eval * pauliMatrix (0 : Fin 4) p * star L.eval) *
                star (layerSequenceEval layers) := by
              simp only [layerSequenceEval, star_mul, mul_assoc]
          _ = pauliMatrix (0 : Fin 4) p' := by rw [hL, hconj]
      · calc
          (pauliSupport p').card = Arithmetic.compressedWeight q (pauliSupport p₁).card r := hweight
          _ = Arithmetic.compressedWeight q (Arithmetic.ceilDiv (pauliSupport p).card q) r := by
            rw [hwL]
          _ = Arithmetic.compressedWeight q (pauliSupport p).card (r + 1) :=
            compressedWeight_shift q (pauliSupport p).card r

theorem pauli_compression_to_arity (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) :
    ∃ layers : List (Layer n (fun _ => 2) q), ∃ p' : Fin n → SinglePauli,
      layers.length = Nat.clog q (pauliSupport p).card - 1 ∧
      layerSequenceEval layers * pauliMatrix (0 : Fin 4) p * star (layerSequenceEval layers) =
        pauliMatrix (0 : Fin 4) p' ∧
      (pauliSupport p').card ≤ q := by
  obtain ⟨layers, p', hlen, hconj, hweight⟩ :=
    pauli_compression_sequence q (by omega) p (Nat.clog q (pauliSupport p).card - 1)
  refine ⟨layers, p', hlen, hconj, ?_⟩
  rw [hweight]
  exact Arithmetic.compressedWeight_at_clog_pred_le q (pauliSupport p).card hq hd

theorem affine_uncompress {α : Type*} [Fintype α] [DecidableEq α]
    (C P Q : Operator α) (hC : IsUnitary C) (hconj : C * P * star C = Q)
    (a b : ℂ) : star C * affine Q a b * C = affine P a b := by
  have hback : star C * Q * C = P := by
    calc
      star C * Q * C = star C * (C * P * star C) * C := by rw [hconj]
      _ = (star C * C) * P * (star C * C) := by simp only [mul_assoc]
      _ = P := by rw [hC.1, one_mul, mul_one]
  calc
    star C * affine Q a b * C =
        a • (star C * C) + b • (star C * Q * C) := by
      simp only [affine, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
    _ = affine P a b := by rw [hC.1, hback]; rfl

/-- A supported unitary middle factor gives one actual compress/rotate/uncompute sequence. -/
theorem affine_synthesis_from_compression
    (layers : List (Layer n (fun _ => 2) q)) (p p' : Fin n → SinglePauli)
    (hn : 0 < n)
    (hconj : layerSequenceEval layers * pauliMatrix (0 : Fin 4) p *
      star (layerSequenceEval layers) = pauliMatrix (0 : Fin 4) p')
    (hweight : (pauliSupport p').card ≤ q) (a b : ℂ)
    (hmid : IsUnitary (affine (pauliMatrix (0 : Fin 4) p') a b)) :
    ∃ output : List (Layer n (fun _ => 2) q),
      output.length = 2 * layers.length + 1 ∧
      layerSequenceEval output = affine (pauliMatrix (0 : Fin 4) p) a b := by
  classical
  let S := pauliSupport p'
  let M := affine (pauliMatrix (0 : Fin 4) p') a b
  have hsupported : SupportedOn M S :=
    (pauliMatrix_supportedOn_pauliSupport p').affine a b
  let middle := singleGateLayer hn S M hweight hsupported hmid
  let output := layers ++ [middle] ++ layers.reverse.map Layer.adjoint
  refine ⟨output, ?_, ?_⟩
  · simp only [output, List.length_append, List.length_singleton, List.length_map,
      List.length_reverse]
    omega
  · calc
      layerSequenceEval output = star (layerSequenceEval layers) * M * layerSequenceEval layers := by
        have huncompute : layerSequenceEval (layers.map Layer.adjoint).reverse =
            star (layerSequenceEval layers) := by
          simpa only [List.map_reverse] using layerSequenceEval_reverse_adjoint layers
        simp [output, middle, layerSequenceEval_append, huncompute,
          layerSequenceEval, singleGateLayer_eval, mul_assoc]
      _ = affine (pauliMatrix (0 : Fin 4) p) a b :=
        affine_uncompress _ _ _ (layerSequenceEval_isUnitary layers) hconj a b

private theorem positive_sites_of_pauli_distance (p : Fin n → SinglePauli)
    (hd : 2 ≤ (pauliSupport p).card) : 0 < n := by
  have hcard : (pauliSupport p).card ≤ n := by
    calc
      (pauliSupport p).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- One compression works for every admissible affine middle gate at the critical depth. -/
theorem pauli_affine_synthesis_data (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) :
    ∃ p' : Fin n → SinglePauli, (pauliSupport p').card ≤ q ∧
      ∀ a b : ℂ, IsUnitary (affine (pauliMatrix (0 : Fin 4) p') a b) →
        ∃ c : Circuit n (fun _ => 2) q (Arithmetic.criticalDepth q (pauliSupport p).card),
          circuitEval c = affine (pauliMatrix (0 : Fin 4) p) a b := by
  classical
  obtain ⟨layers, p', hlen, hconj, hweight⟩ := pauli_compression_to_arity q hq p hd
  refine ⟨p', hweight, ?_⟩
  intro a b hmid
  obtain ⟨output, houtlen, heval⟩ := affine_synthesis_from_compression layers p p'
    (positive_sites_of_pauli_distance p hd) hconj hweight a b hmid
  have hm : 0 < Nat.clog q (pauliSupport p).card :=
    Arithmetic.clog_pos_of_two_le q (pauliSupport p).card hq hd
  have hcritical : output.length = Arithmetic.criticalDepth q (pauliSupport p).card := by
    rw [houtlen, hlen]
    unfold Arithmetic.criticalDepth
    omega
  refine ⟨hcritical ▸ circuitOfLayers output, ?_⟩
  rw [circuitEval_cast, circuitOfLayers_eval]
  exact heval

/-- Every continuous Pauli rotation is realized by an actual critical-depth circuit. -/
theorem pauli_rotation_synthesis (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) (t : ℝ) :
    ∃ c : Circuit n (fun _ => 2) q (Arithmetic.criticalDepth q (pauliSupport p).card),
      circuitEval c = rotation (pauliMatrix (0 : Fin 4) p) t := by
  obtain ⟨p', _hweight, hsynth⟩ := pauli_affine_synthesis_data q hq p hd
  have hmid := rotation_isUnitary (unphased_pauliMatrix_selfAdjoint p')
    (unphased_pauliMatrix_sq p') t
  simpa only [rotation] using hsynth (Real.cos t : ℂ) (Complex.I * (Real.sin t : ℂ)) hmid

/-- The explicit projectively injective rational family has the same exact depth. -/
theorem pauli_rationalRotation_synthesis (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) (r : ℕ) :
    ∃ c : Circuit n (fun _ => 2) q (Arithmetic.criticalDepth q (pauliSupport p).card),
      circuitEval c = rationalRotation (pauliMatrix (0 : Fin 4) p) r := by
  obtain ⟨p', _hweight, hsynth⟩ := pauli_affine_synthesis_data q hq p hd
  have hmid := rationalRotation_isUnitary (unphased_pauliMatrix_selfAdjoint p')
    (unphased_pauliMatrix_sq p') r
  simpa only [rationalRotation] using
    hsynth (rationalScale r) (rationalScale r * Complex.I * (r : ℂ)) hmid

end CriticalDepth.Manuscript
