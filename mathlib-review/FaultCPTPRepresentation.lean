import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Matrix CPTP maps and the finite Kraus model

Complete positivity means positivity after every finite reference
amplification. The Choi matrix of such a map is positive semidefinite,
and its spectral factor gives a finite Kraus family on precisely the
output–input coordinates used for recovery compression. Trace
preservation is equivalent to the Kraus completeness identity.
-/

namespace CriticalDepth.FaultCPTPRepresentation

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker

variable {In Out Ref Kraus : Type*}
variable [Fintype In] [DecidableEq In] [Fintype Out] [DecidableEq Out]

/-- An ordinary complex-linear map on the full finite matrix algebra. -/
abbrev MatrixChannel (In Out : Type*) :=
  Matrix In In ℂ →ₗ[ℂ] Matrix Out Out ℂ

/-- Identity on the finite reference and the given map on each input block. -/
def amplify (L : MatrixChannel In Out) (X : Matrix (Ref × In) (Ref × In) ℂ) :
    Matrix (Ref × Out) (Ref × Out) ℂ :=
  Matrix.of fun p q => L (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2

def IsCompletelyPositive (L : MatrixChannel In Out) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin n × In) (Fin n × In) ℂ,
    X.PosSemidef → (amplify L X).PosSemidef

def IsTracePreserving (L : MatrixChannel In Out) : Prop :=
  ∀ X : Matrix In In ℂ, (L X).trace = X.trace

/-- The reference-first Choi matrix, unnormalized. -/
def choi (L : MatrixChannel In Out) : Matrix (In × Out) (In × Out) ℂ :=
  Matrix.of fun p q => L (Matrix.single p.1 q.1 1) p.2 q.2

private def bell (In : Type*) [DecidableEq In] : In × In → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

private theorem choi_eq_amplify_bell (L : MatrixChannel In Out) :
    choi L = amplify L (vecMulVec (bell In) (star (bell In))) := by
  apply Matrix.ext
  intro p q
  have hblock :
      (Matrix.of fun i j => vecMulVec (bell In) (star (bell In)) (p.1, i) (q.1, j)) =
        Matrix.single p.1 q.1 1 := by
    apply Matrix.ext
    intro i j
    by_cases hi : p.1 = i <;> by_cases hj : q.1 = j <;>
      simp [bell, Matrix.vecMulVec, Matrix.single, hi, hj]
  simp only [choi, amplify, Matrix.of_apply, hblock]

private theorem choi_posSemidef (L : MatrixChannel In Out)
    (hCP : IsCompletelyPositive L) : (choi L).PosSemidef := by
  classical
  let e := Fintype.equivFin In
  let X := vecMulVec (bell In) (star (bell In))
  let X' : Matrix (Fin (Fintype.card In) × In) (Fin (Fintype.card In) × In) ℂ :=
    X.submatrix (Prod.map e.symm id) (Prod.map e.symm id)
  have hX : X.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hX' : X'.PosSemidef := hX.submatrix _
  have h := (hCP (Fintype.card In) X' hX').submatrix (Prod.map e id)
  have hEq : (amplify L X').submatrix (Prod.map e id) (Prod.map e id) = amplify L X := by
    apply Matrix.ext
    intro p q
    simp [amplify, X', Matrix.submatrix_apply]
  rw [hEq, ← choi_eq_amplify_bell] at h
  exact h

private theorem linearMap_eq_of_single (L M : MatrixChannel In Out)
    (h : ∀ i j, L (Matrix.single i j 1) = M (Matrix.single i j 1)) : L = M := by
  apply LinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  have hTerm (i j : In) : L (Matrix.single i j (X i j)) =
      M (Matrix.single i j (X i j)) := by
    have he : Matrix.single i j (X i j) = X i j • (Matrix.single i j 1 : Matrix In In ℂ) := by
      rw [Matrix.smul_single]
      simp
    simp only [he, map_smul, h]
  simp only [map_sum, hTerm]

private def krausTerm (K : Matrix Out In ℂ) : MatrixChannel In Out where
  toFun X := K * X * K.conjTranspose
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- The linear map induced by a finite Kraus family. -/
def krausMap [Fintype Kraus] (K : Kraus → Matrix Out In ℂ) : MatrixChannel In Out :=
  ∑ k, krausTerm (K k)

theorem krausMap_apply [Fintype Kraus] (K : Kraus → Matrix Out In ℂ) (X : Matrix In In ℂ) :
    krausMap K X = ∑ k, K k * X * (K k).conjTranspose := by
  simp [krausMap, krausTerm]

private theorem choi_kraus_entry [Fintype Kraus] (K : Kraus → Matrix Out In ℂ)
    (p q : In × Out) :
    choi (krausMap K) p q = ∑ k, K k p.2 p.1 * star (K k q.2 q.1) := by
  simp only [choi, Matrix.of_apply, krausMap_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_apply, Finset.sum_eq_single q.1]
  · simp only [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]
  · intro j _ hne
    have hz : (K k * Matrix.single p.1 q.1 (1 : ℂ)) p.2 j = 0 :=
      Matrix.mul_single_apply_of_ne (1 : ℂ) p.1 q.1 p.2 j hne (K k)
    rw [hz, zero_mul]
  · simp

private theorem squareFactor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, B * B.conjTranspose = A := by
  let V := hA.1.eigenvectorUnitary
  let sqrtD := Matrix.diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ))
  refine ⟨(V : Matrix ι ι ℂ) * sqrtD, ?_⟩
  have hs : sqrtD.conjTranspose = sqrtD := by
    simp [sqrtD, Matrix.diagonal_conjTranspose, Pi.star_apply, Complex.conj_ofReal]
  have hd : sqrtD * sqrtD = Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ)) := by
    rw [show sqrtD = Matrix.diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) by rfl,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  have hSpectral : (V : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ)) *
      (V : Matrix ι ι ℂ).conjTranspose = A := by
    symm
    simpa only [V, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hA.1.spectral_theorem
  calc
    _ = (V : Matrix ι ι ℂ) * (sqrtD * sqrtD) * (V : Matrix ι ι ℂ).conjTranspose := by
      rw [Matrix.conjTranspose_mul, hs]
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hd, hSpectral]

theorem exists_kraus_of_cp (L : MatrixChannel In Out) (hCP : IsCompletelyPositive L) :
    ∃ K : (In × Out) → Matrix Out In ℂ, L = krausMap K := by
  obtain ⟨B, hB⟩ := squareFactor (choi L) (choi_posSemidef L hCP)
  let K : (In × Out) → Matrix Out In ℂ := fun k => Matrix.of fun b a => B (a, b) k
  refine ⟨K, linearMap_eq_of_single _ _ ?_⟩
  intro i j
  apply Matrix.ext
  intro a b
  have he := congrFun (congrFun hB (i, a)) (j, b)
  rw [show L (Matrix.single i j 1) a b = choi L (i, a) (j, b) from rfl,
    show (krausMap K) (Matrix.single i j 1) a b = choi (krausMap K) (i, a) (j, b) from rfl,
    choi_kraus_entry]
  simpa only [K, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] using he.symm

theorem amplify_kraus [Fintype Kraus] [Fintype Ref] [DecidableEq Ref]
    (K : Kraus → Matrix Out In ℂ) (X : Matrix (Ref × In) (Ref × In) ℂ) :
    amplify (krausMap K) X = ∑ k,
      ((1 : Matrix Ref Ref ℂ) ⊗ₖ K k) * X *
        (((1 : Matrix Ref Ref ℂ) ⊗ₖ K k)).conjTranspose := by
  apply Matrix.ext
  rintro ⟨r, a⟩ ⟨s, b⟩
  simp only [amplify, Matrix.of_apply, krausMap_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hLeft (j : Ref × In) :
      (((1 : Matrix Ref Ref ℂ) ⊗ₖ K k) * X) (r, a) j =
        ∑ i : In, K k a i * X (r, i) j := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single r]
    · simp
    · intro t _ hne
      apply Finset.sum_eq_zero
      intro i _
      simp [Matrix.one_apply, Ne.symm hne]
    · simp
  conv_rhs => rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp only [hLeft, Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul,
      Matrix.mul_apply, Matrix.of_apply]
  · intro t _ hne
    apply Finset.sum_eq_zero
    intro i _
    simp [Matrix.one_apply, Ne.symm hne]
  · simp

theorem kraus_isCompletelyPositive [Fintype Kraus] (K : Kraus → Matrix Out In ℂ) :
    IsCompletelyPositive (krausMap K) := by
  intro n X hX
  rw [amplify_kraus]
  exact Matrix.posSemidef_sum _ fun k _ => hX.mul_mul_conjTranspose_same _

theorem kraus_isTracePreserving_iff [Fintype Kraus] (K : Kraus → Matrix Out In ℂ) :
    IsTracePreserving (krausMap K) ↔ (∑ k, (K k).conjTranspose * K k) = 1 := by
  let S : Matrix In In ℂ := ∑ k, (K k).conjTranspose * K k
  have heq (X : Matrix In In ℂ) : (krausMap K X).trace = (S * X).trace := by
    simp only [krausMap_apply, Matrix.trace_sum, S, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact Matrix.trace_mul_cycle _ _ _
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    have hx := h (Matrix.single j i 1)
    rw [heq] at hx
    have hentry (T : Matrix In In ℂ) :
        (T * Matrix.single j i 1).trace = T i j := by
      unfold Matrix.trace
      rw [Finset.sum_eq_single i]
      · rw [Matrix.diag_apply, Matrix.mul_single_apply_same]
        simp
      · intro a _ ha
        exact Matrix.mul_single_apply_of_ne (1 : ℂ) j i a a ha T
      · simp
    rw [hentry] at hx
    rw [← hentry 1, Matrix.one_mul]
    exact hx
  · intro h X
    rw [heq, show S = 1 from h, Matrix.one_mul]

/-- This is the exact bridge to the finite Kraus model. Both directions
quantify over all logical input matrices and all finite reference sizes. -/
theorem cptp_iff_exists_completeKraus (L : MatrixChannel In Out) :
    (IsCompletelyPositive L ∧ IsTracePreserving L) ↔
      ∃ K : (In × Out) → Matrix Out In ℂ,
        L = krausMap K ∧ (∑ k, (K k).conjTranspose * K k) = 1 := by
  constructor
  · rintro ⟨hc, ht⟩
    obtain ⟨K, rfl⟩ := exists_kraus_of_cp L hc
    exact ⟨K, rfl, (kraus_isTracePreserving_iff K).mp ht⟩
  · rintro ⟨K, rfl, ht⟩
    exact ⟨kraus_isCompletelyPositive K, (kraus_isTracePreserving_iff K).mpr ht⟩

#print axioms exists_kraus_of_cp
#print axioms kraus_isCompletelyPositive
#print axioms kraus_isTracePreserving_iff
#print axioms cptp_iff_exists_completeKraus

end

end CriticalDepth.FaultCPTPRepresentation
