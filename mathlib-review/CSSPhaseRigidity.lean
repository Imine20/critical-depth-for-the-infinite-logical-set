import CSSQuadraticPhase
import CSSPhaseOverlap
import CSSCodeOrthogonality

/-!
# Sign rigidity of the CSS phase

The mixed coordinate signs determine the off-diagonal part of a symmetric
binary matrix. The one-coordinate factors supply its diagonal. Triviality
of the phase on each allowed check direction forces the matrix to send
the X-check space into the Z-check space.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

noncomputable section

open Matrix
open CriticalDepth.Manuscript20261114.CSSCode

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [CommGroup G]

private abbrev e (i : ι) : BinaryWord ι := Pi.single i 1

private theorem bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  by_cases h : a = 0
  · exact Or.inl h
  · have hv := a.val_lt
    have hn : a.val ≠ 0 := fun hz => h ((ZMod.val_eq_zero a).mp hz)
    exact Or.inr ((ZMod.val_eq_one (by decide) a).mp (by omega))

private theorem constant_difference_sum (s : Finset ι) (v : BinaryWord ι → G)
    (a : ι → G) (h : ∀ j ∈ s, ∀ x, phaseDifference (e j) v x = a j)
    (x : BinaryWord ι) :
    v (x + ∑ j ∈ s, e j) = v x * ∏ j ∈ s, a j := by
  have hd : ∀ z, phaseDifference (∑ j ∈ s, e j) v z = ∏ j ∈ s, a j := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      intro z
      rw [Finset.sum_insert hi, Finset.prod_insert hi, phaseDifference_add,
        h i (Finset.mem_insert_self i s),
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
  exact div_eq_iff_eq_mul'.mp (hd x)

private theorem bit_difference_at_own_shift (u : BinaryWord ι → G) (i : ι)
    (x : BinaryWord ι) :
    bitPhaseDifference u i (x + e i) = (bitPhaseDifference u i x)⁻¹ := by
  have h := phaseDifference_add (e i) (e i) u x
  rw [ZModModule.add_self (e i), phaseDifference_zero] at h
  exact eq_inv_of_mul_eq_one_left (by
    simpa only [bitPhaseDifference, mul_comm] using h.symm)

private theorem basis_sum_erase (a : BinaryWord ι) (i : ι) :
    a = (if a i = 0 then 0 else e i) + ∑ j ∈ (binaryWordSupport a).erase i, e j := by
  by_cases hi : a i = 0
  · have hn : i ∉ binaryWordSupport a := by simp [binaryWordSupport, hi]
    rw [ite_eq_left hi, zero_add, Finset.erase_eq_of_notMem hn, sum_basis_on_binaryWordSupport]
  · have hm : i ∈ binaryWordSupport a := by simp [binaryWordSupport, hi]
    rw [ite_eq_right hi, add_comm, Finset.sum_erase_add _ _ hm, sum_basis_on_binaryWordSupport]

private theorem sign_mul (a b : ZMod 2) :
    binaryPhaseSign (a + b) = binaryPhaseSign a * binaryPhaseSign b := by
  rcases bit_cases a with rfl | rfl
  · simp
  rcases bit_cases b with rfl | rfl
  · simp
  rw [show (1 + 1 : ZMod 2) = 0 by decide, binaryPhaseSign_zero, binaryPhaseSign_one]
  apply Units.ext
  simp [Units.val_mul]

private theorem sign_prod (s : Finset ι) (a : ι → ZMod 2) :
    binaryPhaseSign (∑ j ∈ s, a j) = ∏ j ∈ s, binaryPhaseSign (a j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, sign_mul, ih]

private theorem minus_one_ne_one :
    Units.mk0 (-1 : ℂ) (neg_ne_zero.mpr one_ne_zero) ≠ 1 := by
  intro h
  have hh : (-1 : ℂ) = 1 := congrArg (fun z : ℂˣ => (z : ℂ)) h
  norm_num at hh

private theorem sign_eq_one_iff (a : ZMod 2) : binaryPhaseSign a = 1 ↔ a = 0 := by
  rcases bit_cases a with rfl | rfl
  · simp
  · simp [binaryPhaseSign_one, minus_one_ne_one]

private theorem sign_of_square_eq_one (z : ℂˣ) (hz : z * z = 1) :
    ∃ a : ZMod 2, z = binaryPhaseSign a := by
  have hc : (z : ℂ) * (z : ℂ) = 1 := congrArg (fun z : ℂˣ => (z : ℂ)) hz
  rcases mul_self_eq_one_iff.mp hc with hp | hn
  · exact ⟨0, by rw [binaryPhaseSign_zero]; exact Units.ext hp⟩
  · exact ⟨1, by rw [binaryPhaseSign_one]; exact Units.ext hn⟩

private theorem sign_of_mixed (u : BinaryWord ι → ℂˣ) (i j : ι) (hij : i ≠ j)
    (h : ∀ x, mixedBitPhaseDifference u i j x = mixedBitPhaseDifference u i j 0) :
    binaryPhaseSign (mixedPhaseMatrix u i j) = mixedBitPhaseDifference u i j 0 := by
  obtain ⟨a, ha⟩ := sign_of_square_eq_one _ (mixedBitPhaseDifference_square_eq_one u i j h)
  rcases bit_cases a with rfl | rfl
  · rw [binaryPhaseSign_zero] at ha
    rw [(mixedPhaseMatrix_eq_zero_iff u i j hij).mpr ha, binaryPhaseSign_zero, ha]
  · have hne : mixedBitPhaseDifference u i j 0 ≠ 1 := by
      rw [ha, binaryPhaseSign_one]
      exact minus_one_ne_one
    have hQ : mixedPhaseMatrix u i j = 1 := by simp [mixedPhaseMatrix, hij, hne]
    rw [hQ, ha]

/-- The diagonal contribution to the mixed derivative of a check shift. -/
def phaseLinearFactor (u : BinaryWord ι → ℂˣ) (a : BinaryWord ι) (i : ι) : ℂˣ :=
  (if a i = 0 then 1 else (bitPhaseDifference u i 0)⁻¹ * (bitPhaseDifference u i 0)⁻¹) *
    binaryPhaseSign ((mixedPhaseMatrix u *ᵥ a) i)

private theorem phase_sign_sum_erase (u : BinaryWord ι → ℂˣ) (a : BinaryWord ι) (i : ι) :
    (∑ j ∈ (binaryWordSupport a).erase i, mixedPhaseMatrix u i j) =
      (mixedPhaseMatrix u *ᵥ a) i := by
  have hm : (∑ j ∈ (binaryWordSupport a).erase i, mixedPhaseMatrix u i j) =
      ∑ j ∈ binaryWordSupport a, mixedPhaseMatrix u i j := by
    by_cases hi : i ∈ binaryWordSupport a
    · have hs := Finset.sum_erase_add (binaryWordSupport a) (fun j => mixedPhaseMatrix u i j) hi
      simpa only [mixedPhaseMatrix_diag, add_zero] using hs
    · rw [Finset.erase_eq_of_notMem hi]
  rw [hm, Matrix.mulVec, dotProduct]
  calc
    _ = ∑ j ∈ binaryWordSupport a, mixedPhaseMatrix u i j * a j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hn : a j ≠ 0 := (Finset.mem_filter.mp hj).2
      rw [(bit_cases (a j)).resolve_left hn, mul_one]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hz : a j = 0 := by simpa [binaryWordSupport] using hj
      rw [hz, mul_zero]

/-- The exact factor `ηᵢ⁻²ᵅⁱ(-1)^{(Q₀α)ᵢ}` in a check shift. -/
theorem shifted_phase_coordinate_factor (u : BinaryWord ι → ℂˣ)
    (hMixed : ∀ i j, i ≠ j → ∀ x, mixedBitPhaseDifference u i j x =
      mixedBitPhaseDifference u i j 0)
    (a : BinaryWord ι) (i : ι) (x : BinaryWord ι) (hxi : x i = 0) :
    bitPhaseDifference (phaseDifference a u) i x = phaseLinearFactor u a i := by
  have hm := constant_difference_sum ((binaryWordSupport a).erase i)
    (bitPhaseDifference u i) (fun j => binaryPhaseSign (mixedPhaseMatrix u i j))
    (fun j hj y => by
      have hji := Finset.ne_of_mem_erase hj
      change mixedBitPhaseDifference u j i y = _
      rw [mixedBitPhaseDifference_comm u j i y, hMixed i j (Ne.symm hji),
        sign_of_mixed u i j (Ne.symm hji) (hMixed i j (Ne.symm hji))])
  simp_rw [← sign_prod, phase_sign_sum_erase] at hm
  have hx : bitPhaseDifference u i x = bitPhaseDifference u i 0 *
      binaryPhaseSign ((mixedPhaseMatrix u *ᵥ x) i) := by
    have hxsum := constant_difference_sum ((binaryWordSupport x).erase i)
      (bitPhaseDifference u i) (fun j => binaryPhaseSign (mixedPhaseMatrix u i j))
      (fun j hj y => by
        have hji := Finset.ne_of_mem_erase hj
        change mixedBitPhaseDifference u j i y = _
        rw [mixedBitPhaseDifference_comm u j i y, hMixed i j (Ne.symm hji),
          sign_of_mixed u i j (Ne.symm hji) (hMixed i j (Ne.symm hji))]) 0
    rw [zero_add, ← sign_prod, phase_sign_sum_erase] at hxsum
    have hsplit := basis_sum_erase x i
    simp only [hxi, ite_true, zero_add] at hsplit
    rwa [← hsplit] at hxsum
  have hsq (b : ZMod 2) : binaryPhaseSign b * binaryPhaseSign b = 1 := by
    rw [← sign_mul, ZModModule.add_self, binaryPhaseSign_zero]
  rw [show bitPhaseDifference (phaseDifference a u) i x =
      phaseDifference (e i) (phaseDifference a u) x from rfl, phaseDifference_comm]
  change bitPhaseDifference u i (x + a) / bitPhaseDifference u i x = phaseLinearFactor u a i
  have ha_split : x + a = (x + if a i = 0 then 0 else e i) +
      ∑ j ∈ (binaryWordSupport a).erase i, e j := by
    rw [add_assoc, ← basis_sum_erase a i]
  rw [ha_split, hm]
  by_cases hai : a i = 0
  · simp [phaseLinearFactor, hai]
  · simp only [phaseLinearFactor, hai, ite_false, bit_difference_at_own_shift]
    rw [hx]
    calc
      _ = ((bitPhaseDifference u i 0)⁻¹ * (bitPhaseDifference u i 0)⁻¹ *
          binaryPhaseSign ((mixedPhaseMatrix u *ᵥ a) i)) *
          (binaryPhaseSign ((mixedPhaseMatrix u *ᵥ x) i) *
            binaryPhaseSign ((mixedPhaseMatrix u *ᵥ x) i))⁻¹ := by
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        ac_rfl
      _ = _ := by rw [hsq, inv_one, mul_one]

theorem shifted_phase_eq_coordinate_product (u : BinaryWord ι → ℂˣ)
    (hMixed : ∀ i j, i ≠ j → ∀ x, mixedBitPhaseDifference u i j x =
      mixedBitPhaseDifference u i j 0)
    (a x : BinaryWord ι) :
    phaseDifference a u x = phaseDifference a u 0 *
      coordinatePhase (phaseLinearFactor u a) x := by
  have hs (s : Finset ι) :
      phaseDifference a u (∑ i ∈ s, e i) =
        phaseDifference a u 0 * ∏ i ∈ s, phaseLinearFactor u a i := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      let z : BinaryWord ι := ∑ j ∈ s, e j
      have hz : z i = 0 := by
        unfold z
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro j hj
        have hne : i ≠ j := fun h => hi (h.symm ▸ hj)
        exact Pi.single_eq_of_ne hne 1
      rw [Finset.sum_insert hi, add_comm (e i), Finset.prod_insert hi]
      change phaseDifference a u (z + e i) = _
      have hstep := shifted_phase_coordinate_factor u hMixed a i z hz
      change phaseDifference a u (z + e i) / phaseDifference a u z = _ at hstep
      rw [div_eq_iff_eq_mul.mp hstep, show phaseDifference a u z = _ from ih]
      ac_rfl
  have hh := hs (binaryWordSupport x)
  rw [sum_basis_on_binaryWordSupport] at hh
  exact hh

private theorem shifted_factor_is_sign_of_sign_diagonal (u : BinaryWord ι → ℂˣ)
    (d : ι → ZMod 2)
    (hd : ∀ i, (bitPhaseDifference u i 0)⁻¹ * (bitPhaseDifference u i 0)⁻¹ = binaryPhaseSign (d i))
    (a : BinaryWord ι) (i : ι) :
    phaseLinearFactor u a i = binaryPhaseSign (((mixedPhaseMatrix u + Matrix.diagonal d) *ᵥ a) i) := by
  rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, sign_mul]
  unfold phaseLinearFactor
  rcases bit_cases (a i) with hai | hai
  · simp [hai]
  · simp [hai, hd, mul_comm]

private theorem coordinatePhase_eq_sign_dot (v x : BinaryWord ι) :
    coordinatePhase (fun i => binaryPhaseSign (v i)) x = binaryPhaseSign (dotProduct v x) := by
  unfold coordinatePhase
  rw [← sign_prod]
  congr 1
  unfold dotProduct
  calc
    _ = ∑ i ∈ binaryWordSupport x, v i * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hxi := (bit_cases (x i)).resolve_left (Finset.mem_filter.mp hi).2
      rw [hxi, mul_one]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ h
      have hxi : x i = 0 := by simpa [binaryWordSupport] using h
      rw [hxi, mul_zero]

/-- Sparse symmetric exclusion eliminates the quadratic part and forces
every remaining one-bit coefficient to be a sign. Here L is the allowed
codeword space and J is its orthogonal space. -/
theorem phase_is_Pauli_of_sparse_symmetric_exclusion {n R : ℕ}
    (H J : Submodule (ZMod 2) (BinaryWord (Fin n))) (u : BinaryWord (Fin n) → ℂˣ)
    (hMixed : ∀ i j, i ≠ j → ∀ x, mixedBitPhaseDifference u i j x =
      mixedBitPhaseDifference u i j 0)
    (hLocal : ∀ i, wordWeight (fun j => mixedPhaseMatrix u i j) ≤ R)
    (hShift : ∀ a ∈ H, ∀ x ∈ cssOrthogonal J, phaseDifference a u x = 1)
    (hSingle : ∀ i, ∃ a ∈ H, a i = 1)
    (hOverlap : ∀ i, ∃ z z', z ∈ cssOrthogonal J ∧ z' ∈ cssOrthogonal J ∧
      binaryWordSupport z ∩ binaryWordSupport z' = {i})
    (hExclude : ∀ Q : Matrix (Fin n) (Fin n) (ZMod 2), Q.IsSymm →
      (∀ i, wordWeight (fun j => Q i j) ≤ R + 1) →
      (∀ a ∈ H, Q *ᵥ a ∈ J) → Q = 0) :
    ∃ p : BinaryWord (Fin n), ∀ x, u x = u 0 * binaryPhaseSign (dotProduct p x) := by
  classical
  have hTriv (a : BinaryWord (Fin n)) (ha : a ∈ H) (x : BinaryWord (Fin n))
      (hx : x ∈ cssOrthogonal J) : coordinatePhase (phaseLinearFactor u a) x = 1 := by
    have hh := shifted_phase_eq_coordinate_product u hMixed a x
    rw [hShift a ha x hx, hShift a ha 0 (Submodule.zero_mem _), one_mul] at hh
    exact hh.symm
  have hSquare (a : BinaryWord (Fin n)) (ha : a ∈ H) (i : Fin n) :
      phaseLinearFactor u a i * phaseLinearFactor u a i = 1 := by
    obtain ⟨z, z', hz, hz', hp⟩ := hOverlap i
    exact coordinatePhase_square_eq_one_of_single_intersection _ _ (fun x hx => hTriv a ha x hx)
      z z' hz hz' i hp
  have hd (i : Fin n) : ∃ j : ZMod 2,
      (bitPhaseDifference u i 0)⁻¹ * (bitPhaseDifference u i 0)⁻¹ = binaryPhaseSign j := by
    obtain ⟨a, ha, hai⟩ := hSingle i
    apply sign_of_square_eq_one
    calc
      _ = (phaseLinearFactor u a i * phaseLinearFactor u a i) *
          (binaryPhaseSign ((mixedPhaseMatrix u *ᵥ a) i) *
            binaryPhaseSign ((mixedPhaseMatrix u *ᵥ a) i))⁻¹ := by
        have hs : binaryPhaseSign ((mixedPhaseMatrix u *ᵥ a) i) *
            binaryPhaseSign ((mixedPhaseMatrix u *ᵥ a) i) = 1 := by
          rw [← sign_mul, ZModModule.add_self, binaryPhaseSign_zero]
        rw [hs, inv_one, mul_one]
        simp only [phaseLinearFactor, hai, one_ne_zero, ite_false]
        let w := (bitPhaseDifference u i 0)⁻¹ * (bitPhaseDifference u i 0)⁻¹
        let s := binaryPhaseSign ((mixedPhaseMatrix u *ᵥ a) i)
        change w * w = (w * s) * (w * s)
        have he : (w * s) * (w * s) = (w * w) * (s * s) := by ac_rfl
        rw [he, show s * s = 1 from hs, mul_one]
      _ = 1 := by
        rw [hSquare a ha i, ← sign_mul, ZModModule.add_self, binaryPhaseSign_zero, inv_one, one_mul]
  choose d hdiag using hd
  let Q := mixedPhaseMatrix u + Matrix.diagonal d
  have hQsymm : Q.IsSymm := by
    change (mixedPhaseMatrix u + Matrix.diagonal d)ᵀ = _
    rw [Matrix.transpose_add, (show (mixedPhaseMatrix u)ᵀ = _ from mixedPhaseMatrix_isSymm u),
      Matrix.diagonal_transpose]
  have hQweight (i : Fin n) : wordWeight (fun j => Q i j) ≤ R + 1 := by
    have hincl : (Finset.univ.filter fun j => Q i j ≠ 0) ⊆
        insert i (Finset.univ.filter fun j => mixedPhaseMatrix u i j ≠ 0) := by
      intro j hj
      by_cases hij : j = i
      · exact Finset.mem_insert.mpr (Or.inl hij)
      · have hj' := (Finset.mem_filter.mp hj).2
        change mixedPhaseMatrix u i j + Matrix.diagonal d i j ≠ 0 at hj'
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), add_zero] at hj'
        exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩)
    have hCard : (Finset.univ.filter fun j => mixedPhaseMatrix u i j ≠ 0).card =
        wordWeight (fun j => mixedPhaseMatrix u i j) := by
      unfold wordWeight
      congr 1
      ext j
      simp
    have hCardQ : (Finset.univ.filter fun j => Q i j ≠ 0).card =
        wordWeight (fun j => Q i j) := by
      unfold wordWeight
      congr 1
      ext j
      simp
    rw [← hCardQ]
    exact (Finset.card_le_card hincl).trans ((Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (hCard.trans_le (hLocal i)) 1))
  have hQcheck (a : BinaryWord (Fin n)) (ha : a ∈ H) : Q *ᵥ a ∈ J := by
    rw [← cssOrthogonal_involutive J]
    intro x hx
    have h := hTriv a ha x hx
    have hfun : phaseLinearFactor u a = fun i => binaryPhaseSign ((Q *ᵥ a) i) := by
      funext i
      exact shifted_factor_is_sign_of_sign_diagonal u d hdiag a i
    rw [hfun] at h
    rw [coordinatePhase_eq_sign_dot] at h
    exact (sign_eq_one_iff _).mp h
  have hQzero : Q = 0 := hExclude Q hQsymm hQweight hQcheck
  have hd0 (i : Fin n) : d i = 0 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => A i i) hQzero
    simpa [Q, Matrix.diagonal_apply_eq] using h
  have hQ0 : mixedPhaseMatrix u = 0 := by
    ext i j
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => A i j) hQzero
    by_cases he : i = j
    · subst j
      simp
    · simpa [Q, Matrix.diagonal_apply_ne _ he] using h
  have heta (i : Fin n) : ∃ p : ZMod 2, bitPhaseDifference u i 0 = binaryPhaseSign p := by
    apply sign_of_square_eq_one
    have h := hdiag i
    rw [hd0 i, binaryPhaseSign_zero, ← mul_inv, inv_eq_one] at h
    exact h
  choose p hp using heta
  refine ⟨p, fun x => ?_⟩
  rw [phase_eq_quadratic_parity u hMixed x, hQ0]
  have hpoly : quadraticPhaseParity (0 : Matrix (Fin n) (Fin n) (ZMod 2)) x = 0 := by
    simp [quadraticPhaseParity]
  rw [hpoly, binaryPhaseSign_zero, mul_one]
  simp_rw [hp]
  rw [← coordinatePhase, coordinatePhase_eq_sign_dot]

/-- A projecting X-check space produces a word with a prescribed bit. -/
theorem exists_check_with_bit_one {n : ℕ}
    (H : Submodule (ZMod 2) (BinaryWord (Fin n))) (hH : HasProjection H 1) (i : Fin n) :
    ∃ a ∈ H, a i = 1 := by
  obtain ⟨a, ha, haeq⟩ := hH {i} (by simp) (Pi.single i 1)
  exact ⟨a, ha, by simpa only [Pi.single_eq_same] using haeq i (Finset.mem_singleton_self i)⟩

/-- A basis of the Z-check space and its weight bound supply the intersecting
allowed words used by the phase rigidity argument. -/
theorem exists_allowed_words_single_intersection_of_check_rows {n b : ℕ}
    (J : Submodule (ZMod 2) (BinaryWord (Fin n))) (B : Matrix (Fin b) (Fin n) (ZMod 2))
    (hRows : Function.Injective (fun a : Fin b → ZMod 2 => a ᵥ* B))
    (hBasis : ∀ w : BinaryWord (Fin n), w ∈ J ↔ ∃ a : Fin b → ZMod 2, a ᵥ* B = w)
    (hDist : ∀ w ∈ J, w ≠ 0 → b + 1 < wordWeight w) (i : Fin n) :
    ∃ z z', z ∈ cssOrthogonal J ∧ z' ∈ cssOrthogonal J ∧
      binaryWordSupport z ∩ binaryWordSupport z' = {i} := by
  have hKernel (z : BinaryWord (Fin n)) (hz : B *ᵥ z = 0) : z ∈ cssOrthogonal J := by
    apply (cssOrthogonal_mem J z).mpr
    intro w hw
    obtain ⟨a, rfl⟩ := (hBasis w).mp hw
    rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, hz, dotProduct_zero]
  obtain ⟨z, z', hz, hz', hIntersect⟩ := exists_kernel_words_single_intersection B hRows
    (fun w hw hrow => hDist w ((hBasis w).mpr hrow) hw) i
  exact ⟨z, z', hKernel z hz, hKernel z' hz', hIntersect⟩

theorem phase_is_Pauli_of_sparse_symmetric_exclusion_of_check_rows {n R b : ℕ}
    (H J : Submodule (ZMod 2) (BinaryWord (Fin n))) (u : BinaryWord (Fin n) → ℂˣ)
    (hMixed : ∀ i j, i ≠ j → ∀ x, mixedBitPhaseDifference u i j x =
      mixedBitPhaseDifference u i j 0)
    (hLocal : ∀ i, wordWeight (fun j => mixedPhaseMatrix u i j) ≤ R)
    (hShift : ∀ a ∈ H, ∀ x ∈ cssOrthogonal J, phaseDifference a u x = 1)
    (hH : HasProjection H 1)
    (B : Matrix (Fin b) (Fin n) (ZMod 2))
    (hRows : Function.Injective (fun a : Fin b → ZMod 2 => a ᵥ* B))
    (hBasis : ∀ w : BinaryWord (Fin n), w ∈ J ↔ ∃ a : Fin b → ZMod 2, a ᵥ* B = w)
    (hDist : ∀ w ∈ J, w ≠ 0 → b + 1 < wordWeight w)
    (hExclude : ∀ Q : Matrix (Fin n) (Fin n) (ZMod 2), Q.IsSymm →
      (∀ i, wordWeight (fun j => Q i j) ≤ R + 1) →
      (∀ a ∈ H, Q *ᵥ a ∈ J) → Q = 0) :
    ∃ p : BinaryWord (Fin n), ∀ x, u x = u 0 * binaryPhaseSign (dotProduct p x) :=
  phase_is_Pauli_of_sparse_symmetric_exclusion H J u hMixed hLocal hShift
    (exists_check_with_bit_one H hH)
    (exists_allowed_words_single_intersection_of_check_rows J B hRows hBasis hDist) hExclude

#print axioms exists_check_with_bit_one
#print axioms exists_allowed_words_single_intersection_of_check_rows
#print axioms phase_is_Pauli_of_sparse_symmetric_exclusion_of_check_rows

#print axioms shifted_phase_coordinate_factor
#print axioms shifted_phase_eq_coordinate_product
#print axioms phase_is_Pauli_of_sparse_symmetric_exclusion

end
end CriticalDepth.Manuscript20261114.CSSCheckSpaces
