import BarePauliRotations

/-!
# Normalized gauge trace of an encoded operator

The partial trace is taken over the gauge factor in the existing
logical-first tensor convention. Gauge conjugation leaves the
compression unchanged after applying this trace.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript
open Matrix
open scoped BigOperators Kronecker

noncomputable section

variable {K g : ℕ}

def normalizedGaugeTrace : Operator (Fin K × Fin g) →ₗ[ℂ] Operator (Fin K) where
  toFun T a b := (g : ℂ)⁻¹ * ∑ u : Fin g, T (a,u) (b,u)
  map_add' T S := by
    ext a b
    change (g : ℂ)⁻¹ * (∑ u : Fin g, (T (a,u) (b,u) + S (a,u) (b,u))) =
      (g : ℂ)⁻¹ * (∑ u : Fin g, T (a,u) (b,u)) +
      (g : ℂ)⁻¹ * (∑ u : Fin g, S (a,u) (b,u))
    rw [Finset.sum_add_distrib, mul_add]
  map_smul' z T := by
    ext a b
    change (g : ℂ)⁻¹ * (∑ u : Fin g, z * T (a,u) (b,u)) =
      z * ((g : ℂ)⁻¹ * (∑ u : Fin g, T (a,u) (b,u)))
    rw [← Finset.mul_sum, mul_left_comm]

def compressedGaugeTrace {n : ℕ} {dim : Fin n → ℕ} (C : Code n dim K g) :
    Operator (PhysicalBasis n dim) →ₗ[ℂ] Operator (Fin K) where
  toFun T := normalizedGaugeTrace (C.encoding.conjTranspose * T * C.encoding)
  map_add' T S := by
    rw [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' z T := by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_smul]
    rfl

theorem normalizedGaugeTrace_kronecker (A : Operator (Fin K)) (B : Operator (Fin g)) :
    normalizedGaugeTrace (A ⊗ₖ B) = ((g : ℂ)⁻¹ * B.trace) • A := by
  ext a b
  change (g : ℂ)⁻¹ * ∑ u : Fin g, A a b * B u u =
    ((g : ℂ)⁻¹ * B.trace) * A a b
  rw [← Finset.mul_sum]
  unfold Matrix.trace Matrix.diag
  ring

theorem normalizedGaugeTrace_kronecker_one (hg : 0 < g) (A : Operator (Fin K)) :
    normalizedGaugeTrace (A ⊗ₖ (1 : Operator (Fin g))) = A := by
  rw [normalizedGaugeTrace_kronecker, Matrix.trace_one, Fintype.card_fin,
    inv_mul_cancel₀ (by exact_mod_cast hg.ne' : (g : ℂ) ≠ 0), one_smul]

private def gaugeBlock (T : Operator (Fin K × Fin g)) (a b : Fin K) : Operator (Fin g) :=
  fun u v => T (a,u) (b,v)

private theorem gaugeBlock_conjugate (T : Operator (Fin K × Fin g))
    (G H : Operator (Fin g)) (a b : Fin K) :
    gaugeBlock ((1 : Operator (Fin K)) ⊗ₖ G * T * ((1 : Operator (Fin K)) ⊗ₖ H)) a b =
      G * gaugeBlock T a b * H := by
  have hleft (c d : Fin K) :
      gaugeBlock (((1 : Operator (Fin K)) ⊗ₖ G) * T) c d = G * gaugeBlock T c d := by
    ext u v
    change (∑ w : Fin K × Fin g,
      ((1 : Operator (Fin K)) ⊗ₖ G) (c,u) w * T w (d,v)) = _
    simp only [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
      Matrix.mul_apply, gaugeBlock]
    simp [ite_mul]
  ext u v
  change (∑ w : Fin K × Fin g,
    (((1 : Operator (Fin K)) ⊗ₖ G) * T) (a,u) w *
      ((1 : Operator (Fin K)) ⊗ₖ H) w (b,v)) = _
  calc
    _ = ∑ j : Fin K, ∑ t : Fin g,
        (((1 : Operator (Fin K)) ⊗ₖ G) * T) (a,u) (j,t) *
          ((if j = b then (1 : ℂ) else 0) * H t v) := by
      rw [Fintype.sum_prod_type]
      simp only [Matrix.kronecker_apply, Matrix.one_apply]
    _ = ∑ t : Fin g, (gaugeBlock (((1 : Operator (Fin K)) ⊗ₖ G) * T) a b) u t * H t v := by
      simp [gaugeBlock, ite_mul, mul_ite, Finset.sum_ite_eq']
    _ = _ := by
      rw [hleft, Matrix.mul_apply]

theorem normalizedGaugeTrace_gauge_conjugation
    (T : Operator (Fin K × Fin g)) (G H : Operator (Fin g)) (hHG : H * G = 1) :
    normalizedGaugeTrace (((1 : Operator (Fin K)) ⊗ₖ G) * T * ((1 : Operator (Fin K)) ⊗ₖ H)) =
      normalizedGaugeTrace T := by
  ext a b
  change (g : ℂ)⁻¹ * (gaugeBlock (((1 : Operator (Fin K)) ⊗ₖ G) * T *
      ((1 : Operator (Fin K)) ⊗ₖ H)) a b).trace =
    (g : ℂ)⁻¹ * (gaugeBlock T a b).trace
  rw [gaugeBlock_conjugate, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hHG, Matrix.one_mul]

theorem compressedGaugeTrace_eq_zero_of_anticommutes_with_gauge
    {n : ℕ} {dim : Fin n → ℕ} (C : Code n dim K g)
    (P Q : Operator (PhysicalBasis n dim)) (G : Operator (Fin g))
    (hQ : Q * C.encoding = C.encoding * ((1 : Operator (Fin K)) ⊗ₖ G))
    (hself : Q.conjTranspose = Q) (hg : G.conjTranspose * G = 1)
    (hanti : Q * P * Q = -P) :
    compressedGaugeTrace C P = 0 := by
  have hadj : C.encoding.conjTranspose * Q =
      ((1 : Operator (Fin K)) ⊗ₖ G.conjTranspose) * C.encoding.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hQ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hself,
      conjTranspose_kronecker_operators, Matrix.conjTranspose_one] at h
    exact h
  have hgg : G * G.conjTranspose = 1 := by
    exact (mul_eq_one_comm).mp hg
  have htrace : compressedGaugeTrace C (Q * P * Q) = compressedGaugeTrace C P := by
    change normalizedGaugeTrace (C.encoding.conjTranspose * (Q * P * Q) * C.encoding) = _
    have he :
        C.encoding.conjTranspose * (Q * P * Q) * C.encoding =
          ((1 : Operator (Fin K)) ⊗ₖ G.conjTranspose) *
            (C.encoding.conjTranspose * P * C.encoding) * ((1 : Operator (Fin K)) ⊗ₖ G) := by
      calc
        _ = (C.encoding.conjTranspose * Q) * P * (Q * C.encoding) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hadj, hQ]; simp only [Matrix.mul_assoc]
    rw [he, normalizedGaugeTrace_gauge_conjugation _ _ _ hgg]
    rfl
  rw [hanti, map_neg] at htrace
  ext i j
  have he := congrArg (fun T : Operator (Fin K) => T i j) htrace
  change -compressedGaugeTrace C P i j = compressedGaugeTrace C P i j at he
  change compressedGaugeTrace C P i j = 0
  linear_combination (-1/2 : ℂ) * he

#print axioms normalizedGaugeTrace_kronecker_one
#print axioms normalizedGaugeTrace_gauge_conjugation
#print axioms compressedGaugeTrace_eq_zero_of_anticommutes_with_gauge

end

end CriticalDepth.FaultShorSaturation.BaconShor
