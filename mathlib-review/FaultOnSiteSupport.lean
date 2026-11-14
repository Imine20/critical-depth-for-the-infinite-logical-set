import FaultSupportPreserving

/-!
# Tensor products preserve physical supports

The complementary part of an on-site tensor product commutes with an
operator supported on a specified site set. The remaining part conjugates
inside that set. This applies to the on-site Pauli form in CSS rigidity.
-/

open scoped BigOperators ENat

namespace CriticalDepth.FaultSupportPreserving

open CriticalDepth.Arithmetic CriticalDepth.Manuscript CriticalDepth.FaultCircuitSupport
open CriticalDepth.FaultNativeModel

noncomputable section

variable {n : ℕ}

/-- A tensor product with identity factors outside S is the ordinary
tensor-local embedding of its factors on S. -/
theorem supportedOn_tensorEntries_of_outside_one
    (U : Fin n → Operator (Fin 2)) (S : Finset (Fin n))
    (hout : ∀ i ∉ S, U i = 1) :
    SupportedOn (tensorEntries U : Operator (QubitBasis n)) S := by
  classical
  refine ⟨tensorEntries (fun i : S => U i.val), ?_⟩
  ext x y
  let f : Fin n → ℂ := fun i => U i (x i) (y i)
  change (∏ i, f i) = if ∀ i, i ∉ S → x i = y i then ∏ i : S, f i.val else 0
  by_cases hxy : ∀ i, i ∉ S → x i = y i
  · rw [ite_eq_left hxy, Finset.prod_coe_sort S f]
    symm
    apply Finset.prod_subset (Finset.subset_univ S)
    intro i _ hi
    dsimp [f]
    rw [hout i hi, hxy i hi]
    simp
  · rw [ite_eq_right hxy]
    push Not at hxy
    obtain ⟨i, hiS, hi⟩ := hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    dsimp [f]
    rw [hout i hiS]
    simp [hi]

theorem isUnitary_tensorEntries (U : Fin n → Operator (Fin 2))
    (hU : ∀ i, IsUnitary (U i)) :
    IsUnitary (tensorEntries U : Operator (QubitBasis n)) := by
  constructor
  · change (tensorEntries U).conjTranspose * tensorEntries U = 1
    rw [← tensorEntries_conjTranspose, ← tensorEntries_mul]
    have h : (fun i => (U i).conjTranspose * U i) = fun _ => (1 : Operator (Fin 2)) := by
      funext i
      exact (hU i).1
    rw [h, tensorEntries_one]
  · change tensorEntries U * (tensorEntries U).conjTranspose = 1
    rw [← tensorEntries_conjTranspose, ← tensorEntries_mul]
    have h : (fun i => U i * (U i).conjTranspose) = fun _ => (1 : Operator (Fin 2)) := by
      funext i
      exact (hU i).2
    rw [h, tensorEntries_one]

/-- Any product of on-site unitaries preserves the declared support of
every physical operator under conjugation. -/
theorem preservesSupports_tensorEntries (U : Fin n → Operator (Fin 2))
    (hU : ∀ i, IsUnitary (U i)) :
    PreservesSupports (tensorEntries U : Operator (QubitBasis n)) := by
  classical
  intro O S hO
  let V : Fin n → Operator (Fin 2) := fun i => if i ∈ S then U i else 1
  let W : Fin n → Operator (Fin 2) := fun i => if i ∈ S then 1 else U i
  have hV : SupportedOn (tensorEntries V : Operator (QubitBasis n)) S :=
    supportedOn_tensorEntries_of_outside_one V S (fun i hi => ite_eq_right hi)
  have hW : SupportedOn (tensorEntries W : Operator (QubitBasis n)) Sᶜ :=
    supportedOn_tensorEntries_of_outside_one W Sᶜ (by
      intro i hi
      simp [W, show i ∈ S from by simpa using hi])
  have hWu : IsUnitary (tensorEntries W : Operator (QubitBasis n)) := by
    apply isUnitary_tensorEntries
    intro i
    by_cases hi : i ∈ S
    · simpa [W, hi] using (isUnitary_one (ι := Fin 2))
    · simpa [W, hi] using hU i
  have hfac : tensorEntries U = tensorEntries V * tensorEntries W := by
    rw [← tensorEntries_mul]
    congr 1
    funext i
    by_cases hi : i ∈ S <;> simp [V, W, hi]
  have hcancel := hO.conjugate_disjoint hW disjoint_compl_right hWu
  have hprop : propagate (tensorEntries U) O = propagate (tensorEntries V) O := by
    rw [hfac]
    calc
      _ = tensorEntries V *
          (tensorEntries W * O * (tensorEntries W).conjTranspose) *
          (tensorEntries V).conjTranspose := by
        simp only [propagate, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hcancel]; rfl
  rw [hprop]
  exact (hV.mul_same hO).mul_same hV.conjTranspose

/-- Multiplying the physical matrix by a scalar retains support preservation. -/
theorem preservesSupports_smul {U : Operator (QubitBasis n)}
    (hU : PreservesSupports U) (z : ℂ) :
    PreservesSupports (z • U) := by
  intro O S hO
  have hs := (hU O S hO).smul (star z * z)
  simpa only [propagate, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul] using hs

/-- The Pauli tensor product, with an arbitrary overall phase, preserves
all supports on the original qubits. -/
theorem preservesSupports_onsitePauli (p : Fin n → SinglePauli) (z : ℂ) :
    PreservesSupports (z • pauliMatrix (0 : Fin 4) p) := by
  rw [pauliMatrix_zero_eq_tensorEntries]
  exact preservesSupports_smul (preservesSupports_tensorEntries _ (fun i => singlePauli_isUnitary (p i))) z

/-- The sharp upper envelope follows on any stabilizer code with the
on-site Pauli product form for every experiment at the given budget. -/
theorem perCodeExponent_eq_upper_of_onsitePauli {k d q h : ℕ}
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hstab : IsStabilizer C)
    (hdist : HasActualDistance C d) (hd : 2 ≤ d) (hq : 2 ≤ q) (hh : 1 ≤ h)
    (hRigidity : ∀ e : Experiment C q h, ∃ (z : ℂ) (p : Fin n → SinglePauli),
      layerSequenceEval e.layers = z • pauliMatrix (0 : Fin 4) p) :
    perCodeExponent C q h = (FaultDepthArithmetic.upperEnvelope q d h : ℕ∞) := by
  apply perCodeExponent_eq_upper_of_preservesSupports C hstab hdist hd hq hh
  intro e
  obtain ⟨z, p, hp⟩ := hRigidity e
  rw [hp]
  exact preservesSupports_onsitePauli p z

#print axioms preservesSupports_tensorEntries
#print axioms preservesSupports_onsitePauli
#print axioms perCodeExponent_eq_upper_of_onsitePauli

end

end CriticalDepth.FaultSupportPreserving
