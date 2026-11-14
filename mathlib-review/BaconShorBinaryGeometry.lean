import FaultShorSaturation

/-!
# Binary gauge and stabilizer geometry of rectangular Bacon--Shor codes

The row and column parity conditions describe the gauge groups modulo
phases. The orthogonals distinguish dressed and bare logical masks.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open scoped BigOperators

variable {rows columns : ℕ}

def transpose {m b : ℕ} (x : Mask m b) : Mask b m := fun ji => x (ji.2, ji.1)

theorem transpose_transpose (x : Mask rows columns) : transpose (transpose x) = x := rfl

def colParity (x : Mask rows columns) (j : Fin columns) : Bit :=
  rowParity (transpose x) j

def gaugeX (x : Mask rows columns) : Prop := xChecks x
def gaugeZ (z : Mask rows columns) : Prop := xChecks (transpose z)

def centerX (x : Mask rows columns) : Prop := zChecks (transpose x)
def centerZ (z : Mask rows columns) : Prop := zChecks z

def bareCentralizes (x z : Mask rows columns) : Prop :=
  (∀ a, gaugeX a → maskDot z a = 0) ∧ (∀ b, gaugeZ b → maskDot x b = 0)

def dressedCentralizes (x z : Mask rows columns) : Prop :=
  (∀ a, centerX a → maskDot z a = 0) ∧ (∀ b, centerZ b → maskDot x b = 0)

theorem dot_transpose (x z : Mask rows columns) :
    maskDot (transpose x) (transpose z) = maskDot x z := by
  simp only [maskDot, transpose, Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem zOrthogonal_gaugeX_iff (z : Mask rows columns) :
    (∀ a, gaugeX a → maskDot z a = 0) ↔ (∀ i j k, z (i, j) = z (i, k)) := by
  have h := centralizes_iff (0 : Mask rows columns) z
  constructor
  · intro hz
    exact (h.mp ⟨hz, fun b _ => by simp [maskDot]⟩).1
  · intro hz
    have he : centralizes (0 : Mask rows columns) z := h.mpr
      ⟨hz, fun _ _ => by simp [rowParity]⟩
    exact he.1

private theorem xOrthogonal_centerZ_iff (x : Mask rows columns) :
    (∀ b, centerZ b → maskDot x b = 0) ↔ (∀ i j, rowParity x i = rowParity x j) := by
  have h := centralizes_iff x (0 : Mask rows columns)
  constructor
  · intro hx
    exact (h.mp ⟨fun a _ => by simp [maskDot], hx⟩).2
  · intro hx
    have he : centralizes x (0 : Mask rows columns) := h.mpr ⟨fun _ _ _ => rfl, hx⟩
    exact he.2

theorem bareCentralizes_iff (x z : Mask rows columns) :
    bareCentralizes x z ↔
      (∀ j i k, x (i, j) = x (k, j)) ∧ (∀ i j k, z (i, j) = z (i, k)) := by
  have hx : (∀ b, gaugeZ b → maskDot x b = 0) ↔
      (∀ j i k, x (i, j) = x (k, j)) := by
    change _ ↔ ∀ j i k, transpose x (j, i) = transpose x (j, k)
    rw [← zOrthogonal_gaugeX_iff (transpose x)]
    constructor
    · intro h b hb
      rw [show b = transpose (transpose b) from rfl, dot_transpose]
      exact h (transpose b) hb
    · intro h b hb
      have hh := h (transpose b) hb
      rwa [dot_transpose] at hh
  rw [bareCentralizes, hx, zOrthogonal_gaugeX_iff]
  exact and_comm

theorem dressedCentralizes_iff (x z : Mask rows columns) :
    dressedCentralizes x z ↔
      (∀ i j, rowParity x i = rowParity x j) ∧
      (∀ j k, colParity z j = colParity z k) := by
  have hz : (∀ a, centerX a → maskDot z a = 0) ↔
      (∀ j k, colParity z j = colParity z k) := by
    change _ ↔ ∀ j k, rowParity (transpose z) j = rowParity (transpose z) k
    rw [← xOrthogonal_centerZ_iff (transpose z)]
    constructor
    · intro h a ha
      rw [show a = transpose (transpose a) from rfl, dot_transpose]
      exact h (transpose a) ha
    · intro h a ha
      have hh := h (transpose a) ha
      rwa [dot_transpose] at hh
  rw [dressedCentralizes, hz, xOrthogonal_centerZ_iff]
  exact and_comm

theorem centerX_iff (x : Mask rows columns) (r : Fin rows) :
    centerX x ↔ gaugeX x ∧ (∀ j i k, x (i, j) = x (k, j)) := by
  constructor
  · rintro ⟨u, hu, h⟩
    have he (i : Fin rows) (j : Fin columns) : x (i, j) = u j := congrFun h (j, i)
    refine ⟨?_, fun j i k => (he i j).trans (he k j).symm⟩
    intro i
    unfold rowParity
    simp only [he, hu]
  · rintro ⟨hX, hC⟩
    refine ⟨fun j => x (r, j), hX r, ?_⟩
    funext ji
    exact hC ji.1 ji.2 r

theorem centerZ_iff (z : Mask rows columns) (c : Fin columns) :
    centerZ z ↔ gaugeZ z ∧ (∀ i j k, z (i, j) = z (i, k)) := by
  exact centerX_iff (transpose z) c

theorem transpose_support (x z : Mask rows columns) :
    (support (transpose x) (transpose z)).card = (support x z).card := by
  classical
  let e : (Fin rows × Fin columns) ≃ (Fin columns × Fin rows) := Equiv.prodComm _ _
  have h : support (transpose x) (transpose z) = (support x z).map e.toEmbedding := by
    ext ji
    rw [Finset.mem_map_equiv]
    change (ji ∈ Finset.univ.filter (fun ji => transpose x ji ≠ 0 ∨ transpose z ji ≠ 0)) ↔
      (e.symm ji ∈ Finset.univ.filter (fun ij => x ij ≠ 0 ∨ z ij ≠ 0))
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rfl
  rw [h, Finset.card_map]

theorem dressed_below_short_side (x z : Mask rows columns)
    (hc : dressedCentralizes x z) (hwt : (support x z).card < min rows columns) :
    gaugeX x ∧ gaugeZ z := by
  obtain ⟨hX, hZ⟩ := (dressedCentralizes_iff x z).mp hc
  constructor
  · intro i
    by_contra hn
    exact (not_lt_of_ge (rows_le_support_of_nonzero_parity x z hX i hn))
      (hwt.trans_le (min_le_left _ _))
  · intro j
    by_contra hn
    have hbound := rows_le_support_of_nonzero_parity (transpose z) (transpose x) hZ j hn
    have hswap : support z x = support x z := by
      ext ij
      simp [support, or_comm]
    rw [transpose_support, hswap] at hbound
    exact (not_lt_of_ge hbound) (hwt.trans_le (min_le_right _ _))

theorem bare_X_column_weight_bound (x z : Mask rows columns) (hc : bareCentralizes x z)
    (i : Fin rows) (j : Fin columns) (h : x (i, j) ≠ 0) :
    rows ≤ (support x z).card := by
  have hC := (bareCentralizes_iff x z).mp hc
  have hz : ∀ a b c, transpose x (a, b) = transpose x (a, c) := hC.1
  have hw := columns_le_support_of_nonzero_entry (transpose z) (transpose x) hz j i h
  have hswap : support z x = support x z := by ext ij; simp [support, or_comm]
  rwa [transpose_support, hswap] at hw

theorem bare_Z_row_weight_bound (x z : Mask rows columns) (hc : bareCentralizes x z)
    (i : Fin rows) (j : Fin columns) (h : z (i, j) ≠ 0) :
    columns ≤ (support x z).card :=
  columns_le_support_of_nonzero_entry x z ((bareCentralizes_iff x z).mp hc).2 i j h

#print axioms dressedCentralizes_iff
#print axioms bareCentralizes_iff
#print axioms centerX_iff
#print axioms centerZ_iff
#print axioms dressed_below_short_side
#print axioms bare_X_column_weight_bound
#print axioms bare_Z_row_weight_bound

end CriticalDepth.FaultShorSaturation.BaconShor
