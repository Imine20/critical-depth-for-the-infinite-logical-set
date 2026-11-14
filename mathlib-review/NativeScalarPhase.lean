import CriticalDepthMathlib
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Restore the scalar phase of an exact native logical circuit
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix
open scoped Kronecker

noncomputable section

variable {n q r K : ℕ} {dim : Fin n → ℕ}

/-- Multiply the local matrix of a native gate by a unit-modulus scalar.
Its support and arity are unchanged. -/
def rephaseNativeGate (z : unitary ℂ) (G : NativeGateData n dim) : NativeGateData n dim :=
  (G.1, ⟨(z : ℂ) • G.2.val,
    unitary_smul_of_phase _ _ z.property.1 G.2.property⟩)

theorem rephaseNativeGate_allowed (z : unitary ℂ) (G : NativeGateData n dim)
    (hG : NativeGateAllowed q G) : NativeGateAllowed q (rephaseNativeGate z G) :=
  ⟨hG.1, hG.2.smul _⟩

theorem nativeLayerEval_rephase_selected_gate (z : unitary ℂ) (G : NativeGateData n dim)
    (L R : NativeLayer n dim) :
    (nativeLayerEval (L ++ rephaseNativeGate z G :: R)).val =
      (z : ℂ) • (nativeLayerEval (L ++ G :: R)).val := by
  rw [nativeLayerEval_val, nativeLayerEval_val]
  simp only [List.map_append, List.map_cons, List.reverse_append, List.reverse_cons,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one, rephaseNativeGate,
    Matrix.mul_smul, Matrix.smul_mul]

private def scalarGate (z : unitary ℂ) : NativeGateData n dim :=
  (∅, scalarPhaseHom (PhysicalBasis n dim) z)

private theorem scalarGate_allowed (z : unitary ℂ) :
    NativeGateAllowed q (scalarGate (n := n) (dim := dim) z) := by
  change (∅ : Finset (Fin n)).card ≤ q ∧
    SupportedOn ((scalarPhaseHom (PhysicalBasis n dim) z).val) ∅
  rw [scalarPhaseHom_val]
  exact ⟨Nat.zero_le q, (supportedOn_one (dim := dim) ∅).smul _⟩

private theorem nativeLayerAllowed_scalar_cons (z : unitary ℂ) (L : NativeLayer n dim)
    (hL : NativeLayerAllowed q L) : NativeLayerAllowed q (scalarGate z :: L) := by
  constructor
  · intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact scalarGate_allowed z
    · exact hL.1 G hG
  · refine List.pairwise_cons.mpr ⟨?_, hL.2⟩
    intro G _
    exact Finset.disjoint_empty_left G.1

private theorem nativeLayerEval_scalar_cons (z : unitary ℂ) (L : NativeLayer n dim) :
    (nativeLayerEval (scalarGate z :: L)).val = (z : ℂ) • (nativeLayerEval L).val := by
  rw [nativeLayerEval_val, nativeLayerEval_val]
  simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
    mul_one, scalarGate, scalarPhaseHom_val, Matrix.mul_smul, Matrix.mul_one]

private theorem nativeCircuitEval_cons_layer (L : NativeLayer n dim) (c : NativeCircuit n dim r) :
    (nativeCircuitEval (Fin.cons L c)).val =
      (nativeCircuitEval c).val * (nativeLayerEval L).val := by
  rw [nativeCircuitEval_val, nativeCircuitEval_val, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, List.reverse_cons, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]

/-- Restore any scalar phase in a native circuit, with no extra layer
when the circuit has positive depth. A zero-support scalar gate is
disjoint from every existing gate in the first layer. -/
theorem nativeCircuit_restore_scalar (z : unitary ℂ) (c : NativeCircuit n dim r)
    (hc : NativeCircuitAllowed q c) :
    ∃ s ≤ max 1 r, ∃ c' : NativeCircuit n dim s, NativeCircuitAllowed q c' ∧
      (nativeCircuitEval c').val = (z : ℂ) • (nativeCircuitEval c).val := by
  cases r with
  | zero =>
    let empty : NativeCircuit n dim 0 := fun i => Fin.elim0 i
    let c' : NativeCircuit n dim 1 := Fin.cons [scalarGate z] empty
    have hEmpty (u : NativeCircuit n dim 0) : (nativeCircuitEval u).val = 1 := by
      rw [nativeCircuitEval_val, List.ofFn_zero]
      rfl
    refine ⟨1, by decide, c', ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have hFirst : c' 0 = [scalarGate z] := Fin.cons_zero _ _
      rw [hFirst]
      exact nativeLayerAllowed_scalar_cons z [] (by simp [NativeLayerAllowed])
    · change (nativeCircuitEval (Fin.cons (scalarGate z :: []) empty)).val = _
      rw [nativeCircuitEval_cons_layer, nativeLayerEval_scalar_cons, hEmpty empty, hEmpty c,
        Matrix.one_mul]
      rfl
  | succ r =>
    let L := c 0
    let tail : NativeCircuit n dim r := fun i => c i.succ
    have he : Fin.cons L tail = c := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Fin.cons_zero _ _
      · exact Fin.cons_succ _ _ _
    refine ⟨r + 1, le_max_right _ _, Fin.cons (scalarGate z :: L) tail, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]
        exact nativeLayerAllowed_scalar_cons z L (hc 0)
      · rw [Fin.cons_succ]
        exact hc j.succ
    · rw [nativeCircuitEval_cons_layer, nativeLayerEval_scalar_cons, Matrix.mul_smul,
        ← nativeCircuitEval_cons_layer, he]

private theorem finOne_unitary_scalar (Z : Matrix.unitaryGroup (Fin 1) ℂ) :
    ∃ z : unitary ℂ, Z.val = (z : ℂ) • (1 : Operator (Fin 1)) := by
  have hm : star (Z.val 0 0) * Z.val 0 0 = 1 := by
    have hp := congrArg (fun M : Operator (Fin 1) => M 0 0) Z.property.1
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_one,
      Matrix.one_apply_eq] using hp
  let z : unitary ℂ := ⟨Z.val 0 0, ⟨hm, by rw [mul_comm, hm]⟩⟩
  refine ⟨z, ?_⟩
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [z, smul_eq_mul, Matrix.one_apply_eq]

/-- With a one-dimensional gauge, an exact native circuit for the
projective class of A gives a native circuit for A itself. -/
theorem nativeLogicalImage_exact_lift
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin 1) ℂ)
    (A : Matrix.unitaryGroup (Fin K) ℂ) {h : ℕ}
    (hA : projectiveMk (Fin K) A ∈ nativeLogicalImage V q h) :
    ∃ s ≤ max 1 h, ∃ c : NativeCircuit n dim s, NativeCircuitAllowed q c ∧
      (nativeCircuitEval c).val * V = V * (A.val ⊗ₖ (1 : Operator (Fin 1))) := by
  obtain ⟨r, hr, c, hc, W, Z, he, hW⟩ := hA
  obtain ⟨a, ha, hwa⟩ := (projectiveMk_eq_iff (Fin K) W A).mp hW
  obtain ⟨z, hz⟩ := finOne_unitary_scalar Z
  let aU : unitary ℂ := ⟨a, ⟨ha, by rw [mul_comm, ha]⟩⟩
  let b := aU * z
  have hb : (b : ℂ) = a * (z : ℂ) := rfl
  have hphase : (nativeCircuitEval c).val * V =
      (b : ℂ) • (V * (A.val ⊗ₖ (1 : Operator (Fin 1)))) := by
    rw [he, hwa, hz, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, Matrix.mul_smul, ← hb]
  obtain ⟨s, hs, c', hc', hEval⟩ := nativeCircuit_restore_scalar b⁻¹ c hc
  refine ⟨s, hs.trans (max_le_max_left 1 hr), c', hc', ?_⟩
  rw [hEval, Matrix.smul_mul, hphase, smul_smul]
  change ((b⁻¹ * b : unitary ℂ) : ℂ) • _ = _
  rw [inv_mul_cancel]
  change (1 : ℂ) • _ = _
  exact one_smul _ _

#print axioms nativeLayerEval_rephase_selected_gate
#print axioms nativeCircuit_restore_scalar
#print axioms nativeLogicalImage_exact_lift

end

end CriticalDepth.Manuscript20261114
