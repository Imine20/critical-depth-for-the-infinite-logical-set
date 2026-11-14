import CSSSparseSymmetricSampling
import CSSSparseMatrixCounts

/-!
Normalized fixed-matrix bounds and summation by the active row count.
The rank threshold is a quarter of the smaller dimension, which allows a
direct factorization bound on low-rank binary matrices.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

noncomputable section
variable {n : ℕ}

private theorem cancel_binary_probability {x y k l m : ℕ}
    (h : x * 2 ^ m ≤ 2 ^ l * y) (hkl : k + l ≤ m) :
    x * 2 ^ k ≤ y := by
  apply Nat.le_of_mul_le_mul_right _ (show 0 < (2 : ℕ) ^ l from by positivity)
  rw [mul_assoc, ← pow_add]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hkl)).trans
    (h.trans_eq (Nat.mul_comm _ _))

theorem card_plantedQ_low_image_rank_normalized
    (Q : Matrix (Fin n) (Fin n) CSSBit) (p : BW n) (a : ℕ) :
    let r := plantedRank Q p
    Nat.card {G : Fin a → PlantedColumnSpace p //
        columnFinrank a (plantedImageColumns Q p G) ≤ min r a / 4} *
      2 ^ ((r * a) / 10) ≤ Nat.card (Fin a → PlantedColumnSpace p) := by
  let r := plantedRank Q p
  let u := min r a
  let s := u / 4
  have hsr : s ≤ r := (Nat.div_le_self _ _).trans (min_le_left _ _)
  have hmul : (r + a) * u ≤ 2 * (r * a) := by
    rw [add_mul, two_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (min_le_right r a))
      (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left a (min_le_left r a))
  have hfour : 4 * ((r + a) * s) ≤ 2 * (r * a) := by
    calc
      _ = (r + a) * (s * 4) := by ring
      _ ≤ (r + a) * u := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ ≤ _ := hmul
  have hcross : r * a / 10 + (r + a) * s ≤ r * a := by omega
  exact cancel_binary_probability (card_plantedQ_low_image_rank_bound Q p a s hsr) hcross

theorem card_zSamples_containing_image_normalized
    (H L : Submodule CSSBit (BW n)) (a b r : ℕ) (hra : r ≤ n) (haa : a ≤ n)
    (hs : min r a / 4 < Module.finrank CSSBit L)
    (hcodim : 2 * n ≤ 5 * (Module.finrank CSSBit (cssOrthogonal H) - b)) :
    Nat.card {G : Fin b → cssOrthogonal H // L ≤ (zColumnsToWord H G).range} *
      2 ^ ((r * a) / 10) ≤ Nat.card (Fin b → cssOrthogonal H) := by
  let s := Module.finrank CSSBit L
  let N := Module.finrank CSSBit (cssOrthogonal H)
  have hmin : min r a ≤ 4 * s := by omega
  have hra' : r * a ≤ n * min r a := by
    rcases le_total r a with h | h
    · rw [min_eq_left h, Nat.mul_comm r a]
      exact Nat.mul_le_mul_right _ haa
    · rw [min_eq_right h]
      exact Nat.mul_le_mul_right _ hra
  have hprod : 2 * (r * a) ≤ 20 * ((N - b) * s) := by
    calc
      _ ≤ 2 * (n * min r a) := Nat.mul_le_mul_left _ hra'
      _ = (2 * n) * min r a := by ring
      _ ≤ (5 * (N - b)) * (4 * s) := Nat.mul_le_mul hcodim hmin
      _ = _ := by ring
  have hcross : (r * a) / 10 + b * s ≤ N * s := by
    have hb : b ≤ N ∨ n = 0 := by
      by_cases hh : b ≤ N
      · exact Or.inl hh
      · right
        have hz : N - b = 0 := by omega
        change 2 * n ≤ 5 * (N - b) at hcodim
        rw [hz, mul_zero] at hcodim
        omega
    rcases hb with hb | hn
    · have hstep : (N - b) * s + b * s = N * s := by
        rw [← add_mul, Nat.sub_add_cancel hb]
      omega
    · have hA : a = 0 := by omega
      have hs₀ : s = 0 := by
        have hfin : s ≤ n := (Submodule.finrank_le L).trans_eq
          (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
        omega
      simp [hA, hs₀]
  exact cancel_binary_probability (card_zSamples_containing_ambient_le H L b) hcross

theorem rowChangesFrom_zero_eq_nonzeroRows (Q : Matrix (Fin n) (Fin n) CSSBit) :
    rowChangesFrom 0 Q = nonzeroRows Q := by
  ext i
  have hz : (0 : Matrix (Fin n) (Fin n) CSSBit).row i = 0 := rfl
  simp only [mem_rowChangesFrom, nonzeroRows, Finset.mem_filter, Finset.mem_univ,
    true_and, hz]

theorem normalized_symmetric_penalty_mono (u w r a : ℕ) (hw : 0 < w)
    (h : u ≤ 2 * w * r) :
    u * a / (20 * w) ≤ r * a / 10 := by
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  apply Nat.le_of_mul_le_mul_right _ (show 0 < 2 * w by positivity)
  calc
    _ = (u * a / (20 * w)) * (20 * w) := by ring
    _ ≤ u * a := Nat.div_mul_le_self _ _
    _ ≤ (2 * w * r) * a := Nat.mul_le_mul_right _ h
    _ = _ := by ring

theorem nonzeroRows_card_pos (Q : Matrix (Fin n) (Fin n) CSSBit) (hQ : Q ≠ 0) :
    0 < (nonzeroRows Q).card := by
  apply Finset.card_pos.mpr
  by_contra! hn
  apply hQ
  ext i j
  have hi : Q.row i = 0 := by
    by_contra hne
    have hm : i ∈ nonzeroRows Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hn] at hm
    exact Finset.notMem_empty i hm
  exact congrFun hi j


/-- Uniform row-shell union bound for a whole family of candidate matrices.
The per-matrix factor C can account for splitting a bad event into cases. -/
theorem card_symmetric_bad_union_le
    {X : Type*} [Fintype X] (Bad : Matrix (Fin n) (Fin n) CSSBit → X → Prop)
    (n_pos : 0 < n) (w a e k C : ℕ)
    (hsize : n * ((w + 1) * n ^ w) ≤ 2 ^ e)
    (hslack : ∀ u, 0 < u → u ≤ n → e * u + k ≤ u * a / (20 * w))
    (hfixed : ∀ Q : Matrix (Fin n) (Fin n) CSSBit, Q ≠ 0 → Q.IsSymm →
      (∀ i, wordWeight (Q.row i) ≤ w) →
      Nat.card {x : X // Bad Q x} * 2 ^ ((nonzeroRows Q).card * a / (20 * w)) ≤
        C * Fintype.card X) :
    Nat.card {x : X // ∃ Q : Matrix (Fin n) (Fin n) CSSBit,
        Q ≠ 0 ∧ Q.IsSymm ∧ (∀ i, wordWeight (Q.row i) ≤ w) ∧ Bad Q x} * 2 ^ k ≤
      n * (C * Fintype.card X) := by
  classical
  let BM := Matrix (Fin n) (Fin n) CSSBit
  let shells (u : ℕ) : Finset BM := Finset.univ.filter fun Q =>
    (nonzeroRows Q).card = u ∧ Q ≠ 0 ∧ Q.IsSymm ∧ ∀ i, wordWeight (Q.row i) ≤ w
  let bad (Q : BM) : Finset X := Finset.univ.filter (Bad Q)
  let U : Finset ℕ := Finset.Icc 1 n
  have hs (u : ℕ) : (shells u).card ≤ 2 ^ (e * u) := by
    have hsub : shells u ⊆ (Finset.univ.filter fun Q : BM =>
        (rowChangesFrom 0 Q).card = u ∧ ∀ i, wordWeight (Q.row i) ≤ w) := by
      intro Q hQ
      obtain ⟨hu, _, _, hw⟩ := (Finset.mem_filter.mp hQ).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [rowChangesFrom_zero_eq_nonzeroRows]; exact ⟨hu, hw⟩⟩
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := card_sparse_matrices_filter_le 0 w u n_pos
      _ ≤ (2 ^ e) ^ u := Nat.pow_le_pow_left hsize u
      _ = _ := (pow_mul _ _ _).symm
  have hu (u : ℕ) (hu : u ∈ U) :
      ((shells u).biUnion bad).card * 2 ^ k ≤ C * Fintype.card X := by
    have hsl := hslack u (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hu).2
    have hb (Q : BM) (hQ : Q ∈ shells u) :
        (bad Q).card * 2 ^ (k + e * u) ≤ C * Fintype.card X := by
      obtain ⟨he, hne, hsymm, hw⟩ := (Finset.mem_filter.mp hQ).2
      have h := hfixed Q hne hsymm hw
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, he] at h
      apply (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) _)).trans h
      simpa only [Nat.add_comm k] using hsl
    apply Nat.le_of_mul_le_mul_right _ (show 0 < (2 : ℕ) ^ (e * u) from by positivity)
    rw [mul_assoc, ← pow_add]
    calc
      _ ≤ (∑ Q ∈ shells u, (bad Q).card) * 2 ^ (k + e * u) :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ ≤ ∑ _Q ∈ shells u, C * Fintype.card X := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum hb
      _ = (shells u).card * (C * Fintype.card X) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ ≤ _ := by
        exact (Nat.mul_le_mul_right _ (hs u)).trans_eq (Nat.mul_comm _ _)
  let B := Finset.univ.filter fun x : X => ∃ Q : BM,
    Q ≠ 0 ∧ Q.IsSymm ∧ (∀ i, wordWeight (Q.row i) ≤ w) ∧ Bad Q x
  have hB : B ⊆ U.biUnion (fun u => (shells u).biUnion bad) := by
    intro x hx
    obtain ⟨Q, hne, hsymm, hw, hbad⟩ := (Finset.mem_filter.mp hx).2
    have hsizeQ : (nonzeroRows Q).card ∈ U := by
      apply Finset.mem_Icc.mpr
      exact ⟨nonzeroRows_card_pos Q hne, by simpa using Finset.card_le_univ (nonzeroRows Q)⟩
    exact Finset.mem_biUnion.mpr ⟨_, hsizeQ, Finset.mem_biUnion.mpr ⟨Q,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hne, hsymm, hw⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change B.card * _ ≤ _
  calc
    _ ≤ (U.biUnion (fun u => (shells u).biUnion bad)).card * 2 ^ k :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hB)
    _ ≤ (∑ u ∈ U, ((shells u).biUnion bad).card) * 2 ^ k :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, C * Fintype.card X := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hu
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, U, Nat.card_Icc, Nat.add_sub_cancel]

#print axioms card_symmetric_bad_union_le

#print axioms card_plantedQ_low_image_rank_normalized
#print axioms card_zSamples_containing_image_normalized
#print axioms normalized_symmetric_penalty_mono
#print axioms nonzeroRows_card_pos

end
end CriticalDepth.Manuscript20261114.CSSCheckSpaces
