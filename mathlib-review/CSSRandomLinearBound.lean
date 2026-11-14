import CSSSparseLinearSample
import CSSRandomSparseScale

/-!
A planted sample retains at most the unrestricted sparse-linear bad count.
The exact size of the hyperplane sample supplies the conditioning factor.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped BigOperators Matrix

variable {n a : ℕ}

def badSparseLinearSample (p : BW n) (R : ℕ) (G : Fin a → PlantedColumnSpace p) : Prop :=
  badSparseLinearMatrix R (columnsToWord G).toMatrix'

private theorem plantedColumnMatrix_injective (p : BW n) :
    Function.Injective (fun G : Fin a → PlantedColumnSpace p => (columnsToWord G).toMatrix') := by
  intro G D he
  funext j
  apply Subtype.ext
  funext i
  have hk := congrArg (fun M : Matrix (Fin n) (Fin a) CSSBit => M i j) he
  change (columnsToWord G).toMatrix' i j = (columnsToWord D).toMatrix' i j at hk
  rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply] at hk
  let y : Fin a → CSSBit := Pi.single j 1
  have hG (E : Fin a → PlantedColumnSpace p) : columnsToWord E y = (E j).val := by
    change (∑ k, y k • (E k).val) = _
    dsimp only [y]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  change columnsToWord G y i = columnsToWord D y i at hk
  rw [hG, hG] at hk
  exact hk

theorem card_badSparseLinearSample_scaled (p : BW n) (hp : p ≠ 0) (R B : ℕ)
    (hn : 0 < n) (hB : ((R + 1) * (R + 1)) * (2 * B + 1) ≤ a)
    (hcount : n * ((R + 1) * n ^ R) ≤ 2 ^ B)
    (E slack : ℕ) (hNp : n ≤ 2 ^ E) (hSlack : a * a + a + E + slack ≤ n / 2) :
    Nat.card {G : Fin a → PlantedColumnSpace p // badSparseLinearSample p R G} * 2 ^ slack ≤
      Nat.card (Fin a → PlantedColumnSpace p) := by
  classical
  let M := Finset.univ.filter fun A : Matrix (Fin n) (Fin a) CSSBit => badSparseLinearMatrix R A
  let f (G : {G : Fin a → PlantedColumnSpace p // badSparseLinearSample p R G}) : M :=
    ⟨(columnsToWord G.val).toMatrix', Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.property⟩⟩
  have hi : Function.Injective f := fun _ _ he =>
    Subtype.ext (plantedColumnMatrix_injective p (congrArg (fun A : M => A.val) he))
  have hcard := Nat.card_le_card_of_injective f hi
  rw [Nat.card_eq_fintype_card (α := M), Fintype.card_coe] at hcard
  have hmat : M.card * 2 ^ (n / 2) ≤ n * 2 ^ (a * a + a * n) := by
    have h := card_badSparseLinearMatrix_scaled (a := a) R B hn hB hcount
    exact h
  have hN := card_planted_columnSpace p hp
  letI : Fintype (PlantedColumnSpace p) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hN
  have hSpace : Nat.card (Fin a → PlantedColumnSpace p) = 2 ^ ((n - 1) * a) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hN, ← pow_mul]
  let K := a * a + a + E
  have hleft : M.card * 2 ^ (K + slack) ≤ n * 2 ^ (a * a + a * n) :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hSlack)).trans hmat
  have hright : n * 2 ^ (a * a + a * n) ≤ 2 ^ ((n - 1) * a) * 2 ^ K := by
    calc
      _ ≤ 2 ^ E * 2 ^ (a * a + a * n) := Nat.mul_le_mul_right _ hNp
      _ = _ := by
        rw [← pow_add, ← pow_add]
        congr 1
        have h := Nat.mul_sub_left_distrib a n 1
        simp only [mul_one] at h
        dsimp [K]
        rw [Nat.mul_comm (n - 1) a, h]
        have ht : a ≤ a * n := by simpa using Nat.mul_le_mul_left a hn
        omega
  have hsmall : M.card * 2 ^ slack ≤ 2 ^ ((n - 1) * a) := by
    apply Nat.le_of_mul_le_mul_right _ (show (0 : ℕ) < 2 ^ K from by positivity)
    have he : M.card * 2 ^ slack * 2 ^ K = M.card * 2 ^ (K + slack) := by
      rw [pow_add]
      ring
    rw [he]
    exact hleft.trans hright
  rw [hSpace]
  exact (Nat.mul_le_mul_right _ hcard).trans hsmall

#print axioms card_badSparseLinearSample_scaled

end CriticalDepth.Manuscript20261114.CSSCheckSpaces