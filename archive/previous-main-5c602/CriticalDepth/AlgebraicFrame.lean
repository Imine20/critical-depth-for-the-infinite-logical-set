import CriticalDepth.MatrixDerivation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Algebraic frame transfer and finite gate insertions

Inverse matrices are explicit variables. The frame identities themselves do
not require the encoding matrices to be constant under a derivation; the
subsequent circuit application may impose that additional property.

The insertion theorem uses an actual finite sum over the list's gate indices.
The list product is taken in its written matrix order; physical execution
order is obtained by supplying the corresponding reversed gate list.
-/

namespace CriticalDepth

open Matrix
open scoped Kronecker BigOperators

variable {F K Phys Code Log Gauge : Type*}
variable [Field F] [Field K] [Algebra F K]
variable [Fintype Phys] [DecidableEq Phys]
variable [Fintype Code] [DecidableEq Code]
variable [Fintype Log] [DecidableEq Log]
variable [Fintype Gauge] [DecidableEq Gauge]

theorem algebraic_forward_of_backward_frame
    (E : Matrix Code Phys K) (V : Matrix Phys Code K)
    (U Ui H : Matrix Phys Phys K) (T Ti : Matrix Code Code K)
    (hUUi : U * Ui = 1) (_hUiU : Ui * U = 1)
    (hTTi : T * Ti = 1) (_hTiT : Ti * T = 1)
    (hencoded : U * V = V * T) (hdual : E * U = T * E) :
    E * H * V = T * (E * Ui * H * U * V) * Ti := by
  have hleft : T * E * Ui = E := by
    calc
      T * E * Ui = (E * U) * Ui := by rw [← hdual]
      _ = E := by rw [Matrix.mul_assoc, hUUi, Matrix.mul_one]
  have hright : U * V * Ti = V := by
    rw [hencoded, Matrix.mul_assoc, hTTi, Matrix.mul_one]
  calc
    E * H * V = (T * E * Ui) * H * (U * V * Ti) := by rw [hleft, hright]
    _ = T * (E * Ui * H * U * V) * Ti := by simp only [Matrix.mul_assoc]

theorem algebraic_gauge_kronecker_conjugation
    (W Wi : Matrix Log Log K) (Z Zi N : Matrix Gauge Gauge K)
    (hWWi : W * Wi = 1) :
    (W ⊗ₖ Z) * ((1 : Matrix Log Log K) ⊗ₖ N) * (Wi ⊗ₖ Zi) =
      (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) := by
  calc
    (W ⊗ₖ Z) * ((1 : Matrix Log Log K) ⊗ₖ N) * (Wi ⊗ₖ Zi) =
        ((W * 1) ⊗ₖ (Z * N)) * (Wi ⊗ₖ Zi) := by
          rw [← Matrix.mul_kronecker_mul W (1 : Matrix Log Log K) Z N]
    _ = ((W * 1) * Wi) ⊗ₖ ((Z * N) * Zi) :=
      (Matrix.mul_kronecker_mul (W * 1) Wi (Z * N) Zi).symm
    _ = (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) := by rw [mul_one, hWWi]

theorem algebraic_gauge_frame_transfer
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui H : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi N : Matrix Gauge Gauge K)
    (hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hdual : E * U = (W ⊗ₖ Z) * E)
    (hbackward : E * Ui * H * U * V = (1 : Matrix Log Log K) ⊗ₖ N) :
    E * H * V = (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) := by
  have hTTi : (W ⊗ₖ Z) * (Wi ⊗ₖ Zi) = 1 := by
    rw [← Matrix.mul_kronecker_mul W Wi Z Zi, hWWi, hZZi,
      Matrix.one_kronecker_one]
  have hTiT : (Wi ⊗ₖ Zi) * (W ⊗ₖ Z) = 1 := by
    rw [← Matrix.mul_kronecker_mul Wi W Zi Z, hWiW, hZiZ,
      Matrix.one_kronecker_one]
  calc
    E * H * V = (W ⊗ₖ Z) * (E * Ui * H * U * V) * (Wi ⊗ₖ Zi) :=
      algebraic_forward_of_backward_frame E V U Ui H (W ⊗ₖ Z) (Wi ⊗ₖ Zi)
        hUUi hUiU hTTi hTiT hencoded hdual
    _ = (W ⊗ₖ Z) * ((1 : Matrix Log Log K) ⊗ₖ N) * (Wi ⊗ₖ Zi) := by
      rw [hbackward]
    _ = (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) :=
      algebraic_gauge_kronecker_conjugation W Wi Z Zi N hWWi

section GateInsertions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev GateWithInverse (ι : Type*) (K : Type*) :=
  Matrix ι ι K × Matrix ι ι K

def gatePairProduct (gates : List (GateWithInverse ι K)) : Matrix ι ι K :=
  (gates.map Prod.fst).prod

def gatePairInverseProduct (gates : List (GateWithInverse ι K)) : Matrix ι ι K :=
  (gates.reverse.map Prod.snd).prod

@[simp] theorem gatePairProduct_nil : gatePairProduct ([] : List (GateWithInverse ι K)) = 1 := by
  simp [gatePairProduct]

@[simp] theorem gatePairInverseProduct_nil :
    gatePairInverseProduct ([] : List (GateWithInverse ι K)) = 1 := by
  simp [gatePairInverseProduct]

@[simp] theorem gatePairProduct_cons
    (p : GateWithInverse ι K) (gates : List (GateWithInverse ι K)) :
    gatePairProduct (p :: gates) = p.1 * gatePairProduct gates := by
  simp [gatePairProduct]

@[simp] theorem gatePairInverseProduct_cons
    (p : GateWithInverse ι K) (gates : List (GateWithInverse ι K)) :
    gatePairInverseProduct (p :: gates) = gatePairInverseProduct gates * p.2 := by
  simp [gatePairInverseProduct, List.reverse_cons, List.map_append, List.prod_append]

theorem gatePairProduct_mutual_inverse
    (gates : List (GateWithInverse ι K))
    (hgate : ∀ p ∈ gates, p.1 * p.2 = 1 ∧ p.2 * p.1 = 1) :
    gatePairProduct gates * gatePairInverseProduct gates = 1 ∧
      gatePairInverseProduct gates * gatePairProduct gates = 1 := by
  revert hgate
  induction gates with
  | nil =>
      intro hgate
      simp
  | cons p gates ih =>
      intro hgate
      have hp := hgate p (by simp)
      have hg : ∀ q ∈ gates, q.1 * q.2 = 1 ∧ q.2 * q.1 = 1 := by
        intro q hq
        exact hgate q (by simp [hq])
      obtain ⟨hprod, hinv⟩ := ih hg
      simp only [gatePairProduct_cons, gatePairInverseProduct_cons]
      constructor
      · calc
          (p.1 * gatePairProduct gates) * (gatePairInverseProduct gates * p.2) =
              p.1 * (gatePairProduct gates * gatePairInverseProduct gates) * p.2 := by
                simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hprod, mul_one, hp.1]
      · calc
          (gatePairInverseProduct gates * p.2) * (p.1 * gatePairProduct gates) =
              gatePairInverseProduct gates * (p.2 * p.1) * gatePairProduct gates := by
                simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hp.2, mul_one, hinv]

/-- A particular actual conjugated insertion, indexed by the finite gate list. -/
def gateInsertionAt (D : Derivation F K K) :
    (gates : List (GateWithInverse ι K)) → Fin gates.length → Matrix ι ι K
  | [], i => Fin.elim0 i
  | p :: gates, i =>
    Fin.cases (matrixDerivation D p.1 * p.2)
      (fun j => p.1 * gateInsertionAt D gates j * p.2) i

theorem gateInsertion_sum_cons
    (D : Derivation F K K) (p : GateWithInverse ι K)
    (gates : List (GateWithInverse ι K)) :
    (∑ i : Fin (p :: gates).length, gateInsertionAt D (p :: gates) i) =
      matrixDerivation D p.1 * p.2 +
        p.1 * (∑ i : Fin gates.length, gateInsertionAt D gates i) * p.2 := by
  change (∑ i : Fin (gates.length + 1), gateInsertionAt D (p :: gates) i) = _
  rw [Fin.sum_univ_succ]
  simp only [gateInsertionAt, Fin.cases_zero, Fin.cases_succ,
    Finset.mul_sum, Finset.sum_mul]

/-- The genuine finite gate-insertion expansion, with no assumed generator identity. -/
theorem logarithmic_gateProduct_insertion_sum
    (D : Derivation F K K) (gates : List (GateWithInverse ι K))
    (hgate : ∀ p ∈ gates, p.1 * p.2 = 1 ∧ p.2 * p.1 = 1) :
    matrixDerivation D (gatePairProduct gates) * gatePairInverseProduct gates =
      ∑ i : Fin gates.length, gateInsertionAt D gates i := by
  revert hgate
  induction gates with
  | nil =>
      intro hgate
      simp [matrixDerivation_one]
  | cons p gates ih =>
      intro hgate
      have hg : ∀ q ∈ gates, q.1 * q.2 = 1 ∧ q.2 * q.1 = 1 := by
        intro q hq
        exact hgate q (by simp [hq])
      have hprod := (gatePairProduct_mutual_inverse gates hg).1
      rw [gatePairProduct_cons, gatePairInverseProduct_cons,
        logarithmic_product_rule D p.1 (gatePairProduct gates) p.2
          (gatePairInverseProduct gates) hprod,
        gateInsertion_sum_cons]
      rw [ih hg]

end GateInsertions
end CriticalDepth
