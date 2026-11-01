import CriticalDepth.PauliSpan
import CriticalDepth.Support
import CriticalDepth.Rotations

/-!
# A concrete one-block Pauli compression gate

A normalized sum of anticommuting Hermitian involutions conjugates one into
the other. Applying this once, or twice inside the same local matrix, gives a
single allowed gate on any nonempty Pauli block. No qubit or auxiliary register
is removed, and no internal factor is counted as an additional circuit layer.
-/

noncomputable section

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def involutionBisector (P Q : Operator ι) : Operator ι :=
  rationalScale 1 • (P + Q)

theorem involutionBisector_selfAdjoint {P Q : Operator ι}
    (hP : star P = P) (hQ : star Q = Q) :
    star (involutionBisector P Q) = involutionBisector P Q := by
  simp [involutionBisector, star_smul, hP, hQ, star_rationalScale]

theorem involutionBisector_sq {P Q : Operator ι}
    (hP : P * P = 1) (hQ : Q * Q = 1) (hanti : P * Q = -(Q * P)) :
    involutionBisector P Q * involutionBisector P Q = 1 := by
  have ha : (rationalScale 1 * rationalScale 1) * (2 : ℂ) = 1 := by
    have h := rationalScale_sq_mul 1
    norm_num [pow_two] at h
    exact h
  have hsum : (P + Q) * (P + Q) = (2 : ℂ) • (1 : Operator ι) := by
    calc
      (P + Q) * (P + Q) = P * P + (P * Q + Q * P) + Q * Q := by noncomm_ring
      _ = 1 + 0 + 1 := by rw [hP, hQ, hanti, neg_add_cancel]
      _ = (2 : ℂ) • (1 : Operator ι) := by simp [two_smul]
  calc
    involutionBisector P Q * involutionBisector P Q =
        (rationalScale 1 * rationalScale 1) • ((P + Q) * (P + Q)) := by
      simp only [involutionBisector, smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (rationalScale 1 * rationalScale 1) • ((2 : ℂ) • (1 : Operator ι)) := by rw [hsum]
    _ = 1 := by rw [smul_smul, ha, one_smul]

theorem involutionBisector_isUnitary {P Q : Operator ι}
    (hPself : star P = P) (hQself : star Q = Q)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hanti : P * Q = -(Q * P)) :
    IsUnitary (involutionBisector P Q) := by
  constructor
  · rw [involutionBisector_selfAdjoint hPself hQself,
      involutionBisector_sq hP hQ hanti]
  · rw [involutionBisector_selfAdjoint hPself hQself,
      involutionBisector_sq hP hQ hanti]

theorem involutionBisector_conjugates {P Q : Operator ι}
    (hP : P * P = 1) (hQ : Q * Q = 1) (hanti : P * Q = -(Q * P)) :
    involutionBisector P Q * P * involutionBisector P Q = Q := by
  have hraw : (P + Q) * P = Q * (P + Q) := by
    rw [add_mul, mul_add, hP, hQ]
    exact add_comm _ _
  have hinter : involutionBisector P Q * P = Q * involutionBisector P Q := by
    dsimp [involutionBisector]
    rw [smul_mul_assoc, mul_smul_comm, hraw]
  calc
    involutionBisector P Q * P * involutionBisector P Q =
        Q * (involutionBisector P Q * involutionBisector P Q) := by
      rw [hinter, mul_assoc]
    _ = Q := by rw [involutionBisector_sq hP hQ hanti, mul_one]

theorem unitary_mul {U V : Operator ι} (hU : IsUnitary U) (hV : IsUnitary V) :
    IsUnitary (U * V) := by
  constructor
  · rw [star_mul]
    calc
      star V * star U * (U * V) = star V * (star U * U) * V := by
        simp only [mul_assoc]
      _ = 1 := by rw [hU.1, mul_one, hV.1]
  · rw [star_mul]
    calc
      U * V * (star V * star U) = U * (V * star V) * star U := by
        simp only [mul_assoc]
      _ = 1 := by rw [hV.2, mul_one, hU.2]

namespace Manuscript

variable {n : ℕ}

def singleSitePauli (j : Fin n) (a : SinglePauli) : Fin n → SinglePauli :=
  fun i => if i = j then a else .I

theorem singleSitePauli_supportedOn (G : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ G) (a : SinglePauli) :
    SupportedOn (pauliMatrix (0 : Fin 4) (singleSitePauli j a)) G := by
  classical
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  have hij : i ≠ j := by
    intro hij
    subst i
    exact hi hj
  simp [singleSitePauli, hij]

theorem unphased_pauliMatrix_anticommute_single
    (p : Fin n → SinglePauli) (j : Fin n) (a : SinglePauli)
    (hp : p j ≠ .I) (ha : a ≠ .I) (hne : p j ≠ a) :
    pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) (singleSitePauli j a) =
      -(pauliMatrix (0 : Fin 4) (singleSitePauli j a) * pauliMatrix (0 : Fin 4) p) := by
  classical
  have hs : (∏ i, (p i).commutationSign (singleSitePauli j a i)) = -1 := by
    calc
      (∏ i, (p i).commutationSign (singleSitePauli j a i)) =
          (p j).commutationSign a := by
        rw [Finset.prod_eq_single j]
        · simp [singleSitePauli]
        · intro i _hi hij
          simp [singleSitePauli, hij, SinglePauli.commutationSign]
        · simp
      _ = -1 := by simp [SinglePauli.commutationSign, hp, ha, hne]
  simpa only [hs, neg_one_smul] using
    unphased_pauliMatrix_commutation p (singleSitePauli j a)

theorem SupportedOn.involutionBisector {dim : Fin n → ℕ}
    {P Q : Operator (PhysicalBasis n dim)} {G : Finset (Fin n)}
    (hP : SupportedOn P G) (hQ : SupportedOn Q G) :
    SupportedOn (involutionBisector P Q) G := by
  exact (hP.add hQ).smul (rationalScale 1)

/-- A single matrix supported on G compresses its nontrivial Pauli to one Z. -/
theorem pauli_group_to_single_site
    (G : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ G → p i = .I) (j : Fin n) (hj : j ∈ G) (hpj : p j ≠ .I) :
    ∃ U : Operator (QubitBasis n), IsUnitary U ∧ SupportedOn U G ∧
      U * pauliMatrix (0 : Fin 4) p * U.conjTranspose =
        pauliMatrix (0 : Fin 4) (singleSitePauli j .Z) := by
  classical
  let P : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) p
  let Z : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) (singleSitePauli j .Z)
  have hPself : star P = P := unphased_pauliMatrix_selfAdjoint p
  have hZself : star Z = Z := unphased_pauliMatrix_selfAdjoint (singleSitePauli j .Z)
  have hPsq : P * P = 1 := unphased_pauliMatrix_sq p
  have hZsq : Z * Z = 1 := unphased_pauliMatrix_sq (singleSitePauli j .Z)
  have hPsupport : SupportedOn P G := pauliMatrix_supportedOn_of_outside_identity G p hout
  have hZsupport : SupportedOn Z G := singleSitePauli_supportedOn G j hj .Z
  by_cases hpZ : p j = .Z
  · let Q : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) (singleSitePauli j .X)
    have hQself : star Q = Q := unphased_pauliMatrix_selfAdjoint (singleSitePauli j .X)
    have hQsq : Q * Q = 1 := unphased_pauliMatrix_sq (singleSitePauli j .X)
    have hQsupport : SupportedOn Q G := singleSitePauli_supportedOn G j hj .X
    have hPQ : P * Q = -(Q * P) := by
      apply unphased_pauliMatrix_anticommute_single p j .X hpj (by decide)
      simp [hpZ]
    have hQZ : Q * Z = -(Z * Q) := by
      apply unphased_pauliMatrix_anticommute_single (singleSitePauli j .X) j .Z
      · simp [singleSitePauli]
      · decide
      · simp [singleSitePauli]
    let H1 := involutionBisector P Q
    let H2 := involutionBisector Q Z
    have hH1self : star H1 = H1 := involutionBisector_selfAdjoint hPself hQself
    have hH2self : star H2 = H2 := involutionBisector_selfAdjoint hQself hZself
    have hH1 : IsUnitary H1 := involutionBisector_isUnitary hPself hQself hPsq hQsq hPQ
    have hH2 : IsUnitary H2 := involutionBisector_isUnitary hQself hZself hQsq hZsq hQZ
    have h1 : H1 * P * H1 = Q := involutionBisector_conjugates hPsq hQsq hPQ
    have h2 : H2 * Q * H2 = Z := involutionBisector_conjugates hQsq hZsq hQZ
    refine ⟨H2 * H1, unitary_mul hH2 hH1,
      (hQsupport.involutionBisector hZsupport).mul_same
        (hPsupport.involutionBisector hQsupport), ?_⟩
    change (H2 * H1) * P * star (H2 * H1) = Z
    rw [star_mul, hH1self, hH2self]
    calc
      (H2 * H1) * P * (H1 * H2) = H2 * (H1 * P * H1) * H2 := by
        simp only [mul_assoc]
      _ = Z := by rw [h1, h2]
  · have hPZ : P * Z = -(Z * P) :=
      unphased_pauliMatrix_anticommute_single p j .Z hpj (by decide) hpZ
    let H := involutionBisector P Z
    have hHself : star H = H := involutionBisector_selfAdjoint hPself hZself
    refine ⟨H, involutionBisector_isUnitary hPself hZself hPsq hZsq hPZ,
      hPsupport.involutionBisector hZsupport, ?_⟩
    change H * P * star H = Z
    rw [hHself]
    exact involutionBisector_conjugates hPsq hZsq hPZ

end Manuscript
end CriticalDepth
