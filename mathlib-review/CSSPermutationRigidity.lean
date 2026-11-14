import CSSCheckSpaces
import Mathlib.Data.ZMod.Basic

/-!
# Binary permutation rigidity for shallow CSS circuits

The coordinate supports of the output bits bound both the local tests for
coset preservation and the rows of the resulting linear map. The uniform
support of each input-bit flip separately bounds its columns.
-/

open scoped BigOperators Matrix

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev BinaryWord (ι : Type*) := ι → ZMod 2

/-- A function depends on a given set of input coordinates. -/
def DependsOn (S : Finset ι) {A : Type*} (f : BinaryWord ι → A) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

/-- Every prescribed bit pattern on at most r coordinates extends to H. -/
def HasProjection (H : Submodule (ZMod 2) (BinaryWord ι)) (r : ℕ) : Prop :=
  ∀ (S : Finset ι), S.card ≤ r → ∀ x : BinaryWord ι,
    ∃ y ∈ H, ∀ i ∈ S, y i = x i

/-- All nonzero words in the dual have weight strictly greater than r. -/
def DualWeightAbove (H : Submodule (ZMod 2) (BinaryWord ι)) (r : ℕ) : Prop :=
  ∀ w : BinaryWord ι, w ≠ 0 → (∀ x ∈ H, dotProduct w x = 0) → r < wordWeight w

theorem hasProjection_of_dualWeightAbove {H : Submodule (ZMod 2) (BinaryWord ι)} {r : ℕ}
    (hH : DualWeightAbove H r) : HasProjection H r := by
  intro S hS x
  obtain ⟨y, hy, hxy⟩ :=
    exists_word_of_dual_distance H S (r + 1) (Nat.lt_succ_of_le hS) hH
      (fun i => x i.val)
  exact ⟨y, hy, fun i hi => hxy ⟨i, hi⟩⟩

omit [Fintype ι] [DecidableEq ι] in
theorem eq_zero_of_dependence_and_projection {H : Submodule (ZMod 2) (BinaryWord ι)}
    {r : ℕ} {S : Finset ι} (hH : HasProjection H r) (hS : S.card ≤ r)
    {f : BinaryWord ι → ZMod 2} (hdep : DependsOn S f)
    (hzero : ∀ x ∈ H, f x = 0) (x : BinaryWord ι) : f x = 0 := by
  obtain ⟨y, hy, hyx⟩ := hH S hS x
  exact (hdep y x hyx).symm.trans (hzero y hy)

omit [Fintype ι] [DecidableEq ι] in
theorem constant_of_translation_invariant_on_projecting_space
    {H : Submodule (ZMod 2) (BinaryWord ι)} {r : ℕ} {S : Finset ι}
    (hH : HasProjection H r) (hS : S.card ≤ r)
    {f : BinaryWord ι → ZMod 2} (hdep : DependsOn S f)
    (hInv : ∀ a ∈ H, ∀ x, f (x + a) = f x) (x : BinaryWord ι) :
    f x = f 0 := by
  obtain ⟨a, ha, hax⟩ := hH S hS x
  calc
    f x = f a := (hdep a x hax).symm
    _ = f 0 := by simpa only [zero_add] using hInv a ha 0

/-- The finite difference in the j-th input bit. -/
def bitDifference (f : BinaryWord ι → BinaryWord ι)
    (j : ι) (x : BinaryWord ι) : BinaryWord ι :=
  f (x + Pi.single j 1) + f x

private theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have ha := a.val_lt
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  exact hv.imp (ZMod.val_eq_zero a).mp (ZMod.val_eq_one (by decide) a).mp

/-- When every single-bit difference is independent of the input, the
binary map is its matrix of bit differences plus its value at zero. -/
theorem affine_of_constant_bitDifferences (f : BinaryWord ι → BinaryWord ι)
    (hconst : ∀ (j : ι) (x : BinaryWord ι), bitDifference f j x = bitDifference f j 0) :
    ∀ x, f x = (fun i j => bitDifference f j 0 i : Matrix ι ι (ZMod 2)) *ᵥ x + f 0 := by
  classical
  let A : Matrix ι ι (ZMod 2) := fun i j => bitDifference f j 0 i
  have hstep (j : ι) (x : BinaryWord ι) :
      f (x + Pi.single j 1) = f x + bitDifference f j 0 := by
    have hh := congrArg (fun v : BinaryWord ι => v + f x) (hconst j x)
    have hh' : f (x + Pi.single j 1) = bitDifference f j 0 + f x := by
      simpa only [bitDifference, zero_add, add_assoc, ZModModule.add_self, add_zero] using hh
    exact hh'.trans (add_comm _ _)
  have htrail (x : BinaryWord ι) (s : Finset ι) :
      f (∑ j ∈ s, (Pi.single j (x j) : BinaryWord ι)) =
        (∑ j ∈ s, x j • bitDifference f j 0) + f 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      rcases zmod_two_eq_zero_or_one (x j) with hx | hx
      · rw [hx, Pi.single_zero, zero_add, zero_smul, zero_add]
        exact ih
      · rw [hx, one_smul, add_comm (Pi.single j 1), hstep, ih]
        abel
  intro x
  have hx := htrail x Finset.univ
  rw [LinearMap.sum_single_apply] at hx
  have hsum : (∑ j, x j • bitDifference f j 0) = A *ᵥ x := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, A, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hsum] at hx
  exact hx

omit [DecidableEq ι] in
private theorem dotProduct_eq_of_eqOn_nonzero {v x y : BinaryWord ι}
    (hxy : ∀ i, v i ≠ 0 → x i = y i) : dotProduct v x = dotProduct v y := by
  classical
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : v i = 0
  · simp [hi]
  · rw [hxy i hi]

/-- Choose short orthogonality tests for H. A word passing all tests lies in H. -/
structure ShortOrthogonalityTests (H : Submodule (ZMod 2) (BinaryWord ι)) (D : ℕ) where
  tests : Set (BinaryWord ι)
  weight_le : ∀ v ∈ tests, wordWeight v ≤ D
  characterize : ∀ x : BinaryWord ι, x ∈ H ↔ ∀ v ∈ tests, dotProduct v x = 0

/-- Every row and column has small Hamming weight and the matrix induces
an invertible linear action preserving H. -/
def SparseLinearPreserver (H : Submodule (ZMod 2) (BinaryWord ι)) (R : ℕ)
    (A : Matrix ι ι (ZMod 2)) : Prop :=
  Function.Bijective A.mulVec ∧ (∀ i, wordWeight (fun j => A i j) ≤ R) ∧
    (∀ j, wordWeight (fun i => A i j) ≤ R) ∧ A.mulVec '' (H : Set (BinaryWord ι)) = H

/-- The classical binary permutation is affine whenever the coordinate
locality and the source CSS coset and distance constraints hold. -/
theorem exists_sparse_affine_of_coset_preservation
    (H L : Submodule (ZMod 2) (BinaryWord ι)) (R D : ℕ) (hD : 2 ≤ D)
    (T : ShortOrthogonalityTests H D)
    (hH : HasProjection H R) (hL : HasProjection L (R * D))
    (hWeight : ∀ w ∈ H, wordWeight w ≤ R * D → w = 0)
    (f : BinaryWord ι → BinaryWord ι) (hBij : Function.Bijective f)
    (rows cols : ι → Finset ι) (hrows : ∀ i, (rows i).card ≤ R)
    (hcols : ∀ j, (cols j).card ≤ R)
    (hLocal : ∀ i, DependsOn (rows i) (fun x => f x i))
    (hFlip : ∀ j x i, i ∉ cols j → bitDifference f j x i = 0)
    (hCoset : ∀ a ∈ H, ∀ x ∈ L, f (x + a) + f x ∈ H) :
    ∃ A : Matrix ι ι (ZMod 2), SparseLinearPreserver H R A ∧
      ∀ x, f x = A *ᵥ x + f 0 := by
  classical
  have hglobal (a : BinaryWord ι) (ha : a ∈ H) (x : BinaryWord ι) :
      f (x + a) + f x ∈ H := by
    apply (T.characterize _).mpr
    intro v hv
    let supp := Finset.univ.filter fun i => v i ≠ 0
    let S := supp.biUnion rows
    have hsupp : supp.card = wordWeight v := by
      unfold supp wordWeight
      congr 1
      ext i
      simp only [Finset.mem_filter]
    have hS : S.card ≤ R * D := by
      calc
        S.card ≤ ∑ i ∈ supp, (rows i).card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ supp, R := Finset.sum_le_sum fun i _ => hrows i
        _ = R * supp.card := by simp [Nat.mul_comm]
        _ ≤ R * D := Nat.mul_le_mul_left R (hsupp ▸ T.weight_le v hv)
    let test : BinaryWord ι → ZMod 2 := fun y => dotProduct v (f (y + a) + f y)
    have hdep : DependsOn S test := by
      intro y z hyz
      apply dotProduct_eq_of_eqOn_nonzero
      intro i hi
      have hrow : ∀ j ∈ rows i, y j = z j := fun j hj =>
        hyz j (Finset.mem_biUnion.mpr ⟨i, by simp [supp, hi], hj⟩)
      have h1 : f (y + a) i = f (z + a) i :=
        hLocal i _ _ (fun j hj => by simp only [Pi.add_apply, hrow j hj])
      exact congrArg₂ (· + ·) h1 (hLocal i y z hrow)
    exact eq_zero_of_dependence_and_projection hL hS hdep
      (fun y hy => (T.characterize _).mp (hCoset a ha y hy) v hv) x
  have hinv (j : ι) (a : BinaryWord ι) (ha : a ∈ H) (x : BinaryWord ι) :
      bitDifference f j (x + a) = bitDifference f j x := by
    have hmem : bitDifference f j (x + a) + bitDifference f j x ∈ H := by
      have h1 := H.add_mem (hglobal a ha (x + Pi.single j 1)) (hglobal a ha x)
      have hswap : x + a + Pi.single j 1 = x + Pi.single j 1 + a := by abel
      simp only [bitDifference, hswap]
      convert h1 using 1 <;> abel
    have hsmall : wordWeight (bitDifference f j (x + a) + bitDifference f j x) ≤ R := by
      refine (wordWeight_le_of_supported (S := cols j) ?_).trans (hcols j)
      intro i hi
      simp [hFlip j (x + a) i hi, hFlip j x i hi]
    have hRD : R ≤ R * D := by
      calc
        R = R * 1 := (Nat.mul_one R).symm
        _ ≤ R * D := Nat.mul_le_mul_left R (by omega)
    have hzero := hWeight _ hmem (hsmall.trans hRD)
    exact sub_eq_zero.mp (by rwa [ZModModule.sub_eq_add])
  have hconst (j : ι) (x : BinaryWord ι) : bitDifference f j x = bitDifference f j 0 := by
    funext i
    refine constant_of_translation_invariant_on_projecting_space hH (hrows i)
      (f := fun y => bitDifference f j y i) ?_ ?_ x
    · intro y z hyz
      have h1 : f (y + Pi.single j 1) i = f (z + Pi.single j 1) i :=
        hLocal i _ _ (fun l hl => by simp only [Pi.add_apply, hyz l hl])
      exact congrArg₂ (· + ·) h1 (hLocal i y z hyz)
    · intro a ha y
      exact congrFun (hinv j a ha y) i
  let A : Matrix ι ι (ZMod 2) := fun i j => bitDifference f j 0 i
  have hAffine : ∀ x, f x = A *ᵥ x + f 0 := affine_of_constant_bitDifferences f hconst
  refine ⟨A, ⟨?_, ?_, ?_, ?_⟩, hAffine⟩
  · apply Finite.injective_iff_bijective.mp
    intro x y hxy
    apply hBij.1
    rw [hAffine x, hAffine y, hxy]
  · intro i
    refine (wordWeight_le_of_supported (S := rows i) ?_).trans (hrows i)
    intro j hj
    have hsame : ∀ l ∈ rows i, (Pi.single j (1 : ZMod 2) : BinaryWord ι) l = (0 : BinaryWord ι) l := by
      intro l hl
      have hne : l ≠ j := fun h => hj (h ▸ hl)
      exact Pi.single_eq_of_ne hne _
    have hval := hLocal i (Pi.single j 1) 0 hsame
    change (f (0 + Pi.single j 1) + f 0) i = 0
    simp [hval, ZModModule.add_self]
  · intro j
    exact (wordWeight_le_of_supported (S := cols j) (fun i hi => hFlip j 0 i hi)).trans (hcols j)
  · have hAH (x : BinaryWord ι) (hx : x ∈ H) : A *ᵥ x ∈ H := by
      have hh := hglobal x hx 0
      rw [zero_add, hAffine x, add_assoc, ZModModule.add_self, add_zero] at hh
      exact hh
    let F : H → H := fun x => ⟨A *ᵥ x.val, hAH x.val x.property⟩
    have hF : Function.Surjective F := Finite.surjective_of_injective (by
      intro x y hxy
      apply Subtype.ext
      apply hBij.1
      have hxy' : A *ᵥ x.val = A *ᵥ y.val := congrArg Subtype.val hxy
      rw [hAffine x.val, hAffine y.val, hxy'])
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hAH y hy
    · intro hx
      obtain ⟨y, hy⟩ := hF ⟨x, hx⟩
      exact ⟨y.val, y.property, congrArg Subtype.val hy⟩

/-- Excluding nonidentity sparse linear preservers forces the physical
permutation to be a translation. -/
theorem permutation_eq_translation_of_sparse_exclusion
    (H L : Submodule (ZMod 2) (BinaryWord ι)) (R D : ℕ) (hD : 2 ≤ D)
    (T : ShortOrthogonalityTests H D)
    (hH : DualWeightAbove H R) (hL : DualWeightAbove L (R * D))
    (hWeight : ∀ w ∈ H, wordWeight w ≤ R * D → w = 0)
    (f : BinaryWord ι → BinaryWord ι) (hBij : Function.Bijective f)
    (rows cols : ι → Finset ι) (hrows : ∀ i, (rows i).card ≤ R)
    (hcols : ∀ j, (cols j).card ≤ R)
    (hLocal : ∀ i, DependsOn (rows i) (fun x => f x i))
    (hFlip : ∀ j x i, i ∉ cols j → bitDifference f j x i = 0)
    (hCoset : ∀ a ∈ H, ∀ x ∈ L, f (x + a) + f x ∈ H)
    (hExclude : ∀ A, SparseLinearPreserver H R A → A = 1) :
    ∀ x, f x = x + f 0 := by
  obtain ⟨A, hA, hAffine⟩ := exists_sparse_affine_of_coset_preservation H L R D hD T
    (hasProjection_of_dualWeightAbove hH) (hasProjection_of_dualWeightAbove hL)
    hWeight f hBij rows cols hrows hcols hLocal hFlip hCoset
  intro x
  simpa [hExclude A hA] using hAffine x

end

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
