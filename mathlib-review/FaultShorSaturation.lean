import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Binary rectangular Shor code

The masks are those of the lower fault-exponent construction. We describe
the spans directly as even row masks of `X` and even selections of full
`Z` rows. Their joint commutation test is equivalent to equal `X` row
parities and `Z` entries constant along each row.
-/

open scoped BigOperators

namespace CriticalDepth.FaultShorSaturation

abbrev Bit := ZMod 2
abbrev Mask (rows columns : ℕ) := Fin rows × Fin columns → Bit

variable {rows columns : ℕ}

def rowParity (a : Mask rows columns) (i : Fin rows) : Bit :=
  ∑ j : Fin columns, a (i, j)

def repeatRows (a : Fin rows → Bit) : Mask rows columns :=
  fun ij => a ij.1

def maskDot (a b : Mask rows columns) : Bit :=
  ∑ ij : Fin rows × Fin columns, a ij * b ij

def xChecks (a : Mask rows columns) : Prop :=
  ∀ i, rowParity a i = 0

def zChecks (a : Mask rows columns) : Prop :=
  ∃ u : Fin rows → Bit, (∑ i, u i) = 0 ∧ a = repeatRows u

def centralizes (x z : Mask rows columns) : Prop :=
  (∀ a, xChecks a → maskDot z a = 0) ∧
    (∀ b, zChecks b → maskDot x b = 0)

private theorem bit_add_self (x : Bit) : x + x = 0 := by
  have ht : (2 : Bit) = 0 := by decide
  rw [← two_mul, ht, zero_mul]

private theorem bit_eq_of_add_eq_zero {x y : Bit} (h : x + y = 0) : x = y := by
  have h' := congrArg (fun t : Bit => x + t) h
  simpa only [← add_assoc, bit_add_self, zero_add, add_zero] using h'.symm

private theorem dot_repeatRows (a : Mask rows columns) (u : Fin rows → Bit) :
    maskDot a (repeatRows u) = ∑ i : Fin rows, rowParity a i * u i := by
  simp only [maskDot, Fintype.sum_prod_type, repeatRows, rowParity, Finset.sum_mul]

private theorem dot_comm (a b : Mask rows columns) :
    maskDot a b = maskDot b a := by
  simp only [maskDot, mul_comm]

private theorem x_checksum_disjoint (a : Mask rows columns) (ha : xChecks a)
    (b : Mask rows columns) (hb : zChecks b) : maskDot a b = 0 := by
  obtain ⟨u, hu, rfl⟩ := hb
  rw [dot_repeatRows]
  simp_rw [show ∀ i, rowParity a i = 0 from ha, zero_mul, Finset.sum_const_zero]

private def site (ij : Fin rows × Fin columns) : Mask rows columns :=
  Pi.single ij 1

private theorem dot_site (a : Mask rows columns) (ij : Fin rows × Fin columns) :
    maskDot a (site ij) = a ij := by
  simp [maskDot, site, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

private theorem dot_add_right (a b c : Mask rows columns) :
    maskDot a (b + c) = maskDot a b + maskDot a c := by
  simp [maskDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem x_check_pair (i : Fin rows) (j k : Fin columns) :
    xChecks (site (i, j) + site (i, k)) := by
  intro r
  by_cases h : i = r
  · subst r
    simp [rowParity, site, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq',
      bit_add_self]
  · simp [rowParity, site, Pi.single_apply, h, Ne.symm h]

private theorem z_check_pair (i j : Fin rows) :
    zChecks (repeatRows (Pi.single i 1 + Pi.single j 1) : Mask rows columns) := by
  refine ⟨Pi.single i 1 + Pi.single j 1, ?_, rfl⟩
  simp [Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq', bit_add_self]

/-- Exact commutation conditions against the two Shor check spaces. -/
theorem centralizes_iff (x z : Mask rows columns) :
    centralizes x z ↔
      (∀ i j k, z (i, j) = z (i, k)) ∧
      (∀ i j, rowParity x i = rowParity x j) := by
  constructor
  · rintro ⟨hx, hz⟩
    refine ⟨?_, ?_⟩
    · intro i j k
      have h := hx _ (x_check_pair i j k)
      rw [dot_add_right, dot_site, dot_site] at h
      exact bit_eq_of_add_eq_zero h
    · intro i j
      have h := hz _ (z_check_pair (columns := columns) i j)
      rw [dot_repeatRows] at h
      apply bit_eq_of_add_eq_zero
      simpa [Pi.add_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib,
        mul_ite, Finset.sum_ite_eq'] using h
  · rintro ⟨hz, hx⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      cases isEmpty_or_nonempty (Fin columns) with
      | inl hempty =>
        simp [maskDot, Fintype.sum_prod_type]
      | inr hcols =>
        let j := Classical.choice hcols
        have heq : z = repeatRows (fun i => z (i, j)) := by
          ext ⟨i, k⟩
          exact hz i k j
        rw [dot_comm, heq, dot_repeatRows]
        simp_rw [show ∀ i, rowParity a i = 0 from ha, zero_mul, Finset.sum_const_zero]
    · intro b hb
      obtain ⟨u, hu, rfl⟩ := hb
      rw [dot_repeatRows]
      cases isEmpty_or_nonempty (Fin rows) with
      | inl hempty => simp
      | inr hrows =>
        let i := Classical.choice hrows
        simp_rw [hx _ i]
        rw [← Finset.mul_sum, hu, mul_zero]

/-- The two binary CSS stabilizer spaces commute. -/
theorem check_spaces_commute {x z : Mask rows columns} (hx : xChecks x) (hz : zChecks z) :
    maskDot x z = 0 :=
  x_checksum_disjoint x hx z hz

def support (x z : Mask rows columns) : Finset (Fin rows × Fin columns) :=
  Finset.univ.filter (fun ij => x ij ≠ 0 ∨ z ij ≠ 0)

/-- If one row parity is nonzero, every row contributes to the support. -/
theorem rows_le_support_of_nonzero_parity (x z : Mask rows columns)
    (hx : ∀ i j, rowParity x i = rowParity x j)
    (i : Fin rows) (hi : rowParity x i ≠ 0) :
    rows ≤ (support x z).card := by
  classical
  have existsCol (r : Fin rows) : ∃ j, x (r, j) ≠ 0 := by
    by_contra! hall
    apply hi
    rw [hx i r]
    simp [rowParity, hall]
  choose col hcol using existsCol
  let pick (r : Fin rows) : support x z := ⟨(r, col r), by simp [support, hcol r]⟩
  have hInjective : Function.Injective pick := fun a b h =>
    congrArg (fun ij : support x z => ij.val.1) h
  simpa using Fintype.card_le_of_injective pick hInjective

/-- A nonzero column entry of a row-constant `Z` mask fills its row. -/
theorem columns_le_support_of_nonzero_entry (x z : Mask rows columns)
    (hz : ∀ i j k, z (i, j) = z (i, k))
    (i : Fin rows) (j : Fin columns) (hj : z (i, j) ≠ 0) :
    columns ≤ (support x z).card := by
  let pick (k : Fin columns) : support x z :=
    ⟨(i, k), by simp [support, hz i k j, hj]⟩
  have hInjective : Function.Injective pick := fun a b h =>
    congrArg (fun ij : support x z => ij.val.2) h
  simpa using Fintype.card_le_of_injective pick hInjective

/-- Every commuting mask below the claimed distance is in the two check spaces. -/
theorem below_min_distance_trivial (x z : Mask rows columns)
    (hC : centralizes x z) (hweight : (support x z).card < min rows columns) :
    xChecks x ∧ zChecks z := by
  obtain ⟨hz, hx⟩ := (centralizes_iff x z).mp hC
  refine ⟨?_, ?_⟩
  · intro i
    by_contra hi
    have hrows := rows_le_support_of_nonzero_parity x z hx i hi
    exact (Nat.not_lt_of_ge hrows) (hweight.trans_le (min_le_left _ _))
  · refine ⟨0, by simp, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    change z (i, j) = 0
    by_contra hj
    have hcols := columns_le_support_of_nonzero_entry x z hz i j hj
    exact (Nat.not_lt_of_ge hcols) (hweight.trans_le (min_le_right _ _))


/-- A full row is the standard minimum-weight (Z) witness. -/
def fullZRow (i : Fin rows) : Mask rows columns :=
  repeatRows (Pi.single i 1)

/-- A full column is the standard (X) witness. -/
def fullXColumn (j : Fin columns) : Mask rows columns :=
  fun ij => if ij.2 = j then 1 else 0

theorem fullZRow_centralizes (i : Fin rows) :
    centralizes (0 : Mask rows columns) (fullZRow i) :=
  (centralizes_iff _ _).2 ⟨by intros; rfl, by simp [rowParity]⟩

theorem fullZRow_not_check (i : Fin rows) (j : Fin columns) :
    ¬ zChecks (fullZRow (columns := columns) i) := by
  rintro ⟨u, hu, heq⟩
  have h : Pi.single i (1 : Bit) = u := by
    funext k
    exact congrFun heq (k, j)
  rw [← h] at hu
  simp [Pi.single_apply, Finset.sum_ite_eq'] at hu

theorem fullXColumn_centralizes (j : Fin columns) :
    centralizes (fullXColumn (rows := rows) j) (0 : Mask rows columns) := by
  apply (centralizes_iff _ _).2
  refine ⟨by intros; rfl, ?_⟩
  intro a b
  simp [rowParity, fullXColumn, Pi.single_apply, Finset.sum_ite_eq']

theorem fullXColumn_not_check (i : Fin rows) (j : Fin columns) :
    ¬ xChecks (fullXColumn (rows := rows) j) := by
  intro hx
  have h := hx i
  simp [rowParity, fullXColumn, Pi.single_apply, Finset.sum_ite_eq'] at h

theorem fullZRow_weight (i : Fin rows) :
    (support (0 : Mask rows columns) (fullZRow i)).card = columns := by
  classical
  let row : Fin columns ↪ Fin rows × Fin columns :=
    ⟨fun j => (i, j), fun a b h => congrArg Prod.snd h⟩
  have heq : support (0 : Mask rows columns) (fullZRow i) =
      (Finset.univ : Finset (Fin columns)).map row := by
    ext ⟨a, b⟩
    by_cases h : i = a
    · subst a
      exact iff_of_true (by simp [support, fullZRow, repeatRows])
        (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)
    · constructor
      · simp [support, fullZRow, repeatRows, Pi.single_apply, h, Ne.symm h]
      · intro hm
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
        exact False.elim (h (congrArg Prod.fst hj))
  rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem fullXColumn_weight (j : Fin columns) :
    (support (fullXColumn j) (0 : Mask rows columns)).card = rows := by
  classical
  let column : Fin rows ↪ Fin rows × Fin columns :=
    ⟨fun i => (i, j), fun a b h => congrArg Prod.fst h⟩
  have heq : support (fullXColumn j) (0 : Mask rows columns) =
      (Finset.univ : Finset (Fin rows)).map column := by
    ext ⟨a, b⟩
    by_cases h : j = b
    · subst b
      exact iff_of_true (by simp [support, fullXColumn])
        (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    · constructor
      · simp [support, fullXColumn, Pi.single_apply, h, Ne.symm h]
      · intro hm
        obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hm
        exact False.elim (h (congrArg Prod.snd hi))
  rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The least support size of a nonstabilizer in the binary centralizer is
the shorter side of the rectangle. -/
theorem binary_distance (i : Fin rows) (j : Fin columns) :
    IsLeast {w : ℕ | ∃ x z : Mask rows columns,
      centralizes x z ∧ ¬ (xChecks x ∧ zChecks z) ∧ w = (support x z).card}
      (min rows columns) := by
  constructor
  · by_cases hc : columns ≤ rows
    · exact ⟨0, fullZRow i, fullZRow_centralizes i,
        fun h => fullZRow_not_check i j h.2,
        (min_eq_right hc).trans (fullZRow_weight i).symm⟩
    · have hr : rows ≤ columns := le_of_lt (lt_of_not_ge hc)
      exact ⟨fullXColumn j, 0, fullXColumn_centralizes j,
        fun h => fullXColumn_not_check i j h.1,
        (min_eq_left hr).trans (fullXColumn_weight j).symm⟩
  · rintro w ⟨x, z, hC, hNot, rfl⟩
    exact le_of_not_gt (fun hlt => hNot (below_min_distance_trivial x z hC hlt))

/-- Apply the same linear row transformation in every column. -/
def acrossColumns (T : (Fin rows → Bit) →ₗ[Bit] (Fin rows → Bit))
    (a : Mask rows columns) : Mask rows columns :=
  fun ij => T (fun i => a (i, ij.2)) ij.1

theorem rowParity_acrossColumns (T : (Fin rows → Bit) →ₗ[Bit] (Fin rows → Bit))
    (a : Mask rows columns) :
    (fun i => rowParity (acrossColumns T a) i) = T (fun i => rowParity a i) := by
  have hfun : (fun i => rowParity a i) = ∑ j : Fin columns, (fun i => a (i, j)) := by
    funext i
    simp [rowParity, Finset.sum_apply]
  rw [hfun, map_sum]
  funext i
  simp [rowParity, acrossColumns, Finset.sum_apply]

theorem acrossColumns_preserves_xChecks
    (T : (Fin rows → Bit) →ₗ[Bit] (Fin rows → Bit))
    (a : Mask rows columns) (ha : xChecks a) :
    xChecks (acrossColumns T a) := by
  have ha0 : (fun i => rowParity a i) = 0 := funext ha
  have h := rowParity_acrossColumns T a
  rw [ha0, map_zero] at h
  exact congrFun h

theorem acrossColumns_fixes_fullXColumn
    (T : (Fin rows → Bit) →ₗ[Bit] (Fin rows → Bit))
    (hT : T (1 : Fin rows → Bit) = 1) (j : Fin columns) :
    acrossColumns T (fullXColumn j) = fullXColumn j := by
  funext ij
  rcases ij with ⟨i, k⟩
  by_cases h : k = j
  · subst k
    have hone : (fun a => fullXColumn (rows := rows) j (a, j)) = 1 := by
      funext a
      simp [fullXColumn]
    change T (fun a => fullXColumn (rows := rows) j (a, j)) i = _
    rw [hone, hT]
    simp [fullXColumn]
  · have hcol : (fun a => fullXColumn (rows := rows) j (a, k)) = 0 := by
      funext a
      simp [fullXColumn, Pi.single_apply, h, Ne.symm h]
    change T (fun a => fullXColumn (rows := rows) j (a, k)) i = _
    rw [hcol, map_zero]
    simp [fullXColumn, Pi.single_apply, h, Ne.symm h]

#print axioms binary_distance
#print axioms rowParity_acrossColumns
#print axioms acrossColumns_preserves_xChecks
#print axioms acrossColumns_fixes_fullXColumn
#print axioms centralizes_iff
#print axioms check_spaces_commute
#print axioms below_min_distance_trivial

end CriticalDepth.FaultShorSaturation
