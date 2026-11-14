import CSSCodeStabilizer

/-!
# Binary masks and commutation of physical CSS Pauli words
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript
open scoped BigOperators

variable {n : ℕ}

private def px : SinglePauli → CSSBit
  | .I | .Z => 0
  | .X | .Y => 1

private def pz : SinglePauli → CSSBit
  | .I | .X => 0
  | .Z | .Y => 1

def cssMaskX (p : Fin n → SinglePauli) : CSSWord n := fun i => px (p i)
def cssMaskZ (p : Fin n → SinglePauli) : CSSWord n := fun i => pz (p i)

private theorem bit_zero_or_one (t : CSSBit) : t = 0 ∨ t = 1 := by decide +revert

theorem cssMaskX_weight_le (p : Fin n → SinglePauli) :
    CSSCheckSpaces.wordWeight (cssMaskX p) ≤ (pauliSupport p).card := by
  apply CSSCheckSpaces.wordWeight_le_of_supported
  intro i hi
  have hp : p i = .I := by
    by_contra hn
    exact hi (by simp [pauliSupport, hn])
  simp [cssMaskX, hp, px]

theorem cssMaskZ_weight_le (p : Fin n → SinglePauli) :
    CSSCheckSpaces.wordWeight (cssMaskZ p) ≤ (pauliSupport p).card := by
  apply CSSCheckSpaces.wordWeight_le_of_supported
  intro i hi
  have hp : p i = .I := by
    by_contra hn
    exact hi (by simp [pauliSupport, hn])
  simp [cssMaskZ, hp, pz]

theorem cssX_commutation (a : CSSWord n) (p : Fin n → SinglePauli) :
    pauliMatrix 0 (cssXWord a) * pauliMatrix 0 p =
      cssSign (dotProduct (cssMaskZ p) a) • (pauliMatrix 0 p * pauliMatrix 0 (cssXWord a)) := by
  rw [unphased_pauliMatrix_commutation]
  congr 1
  unfold dotProduct
  rw [cssSign_sum]
  apply Finset.prod_congr rfl
  intro i _
  change (if a i = 0 then SinglePauli.I else SinglePauli.X).commutationSign (p i) =
    cssSign (pz (p i) * a i)
  generalize a i = b
  generalize p i = t
  rcases bit_zero_or_one b with (rfl | rfl) <;> cases t <;>
    simp [SinglePauli.commutationSign, cssSign, pz]

theorem cssZ_commutation (a : CSSWord n) (p : Fin n → SinglePauli) :
    pauliMatrix 0 (cssZWord a) * pauliMatrix 0 p =
      cssSign (dotProduct (cssMaskX p) a) • (pauliMatrix 0 p * pauliMatrix 0 (cssZWord a)) := by
  rw [unphased_pauliMatrix_commutation]
  congr 1
  unfold dotProduct
  rw [cssSign_sum]
  apply Finset.prod_congr rfl
  intro i _
  change (if a i = 0 then SinglePauli.I else SinglePauli.Z).commutationSign (p i) =
    cssSign (px (p i) * a i)
  generalize a i = b
  generalize p i = t
  rcases bit_zero_or_one b with (rfl | rfl) <;> cases t <;>
    simp [SinglePauli.commutationSign, cssSign, px]

theorem eq_identity_of_zero_cssMasks (p : Fin n → SinglePauli)
    (hx : cssMaskX p = 0) (hz : cssMaskZ p = 0) :
    pauliMatrix 0 p = 1 := by
  have hp : p = fun _ => .I := by
    funext i
    have ha := congrFun hx i
    have hb := congrFun hz i
    cases h : p i <;> simp [cssMaskX, cssMaskZ, px, pz, h] at ha hb ⊢
  rw [hp, pauliMatrix_zero_eq_tensorEntries]
  exact tensorEntries_one

theorem cssZWord_support_card (a : CSSWord n) :
    (pauliSupport (cssZWord a)).card = CSSCheckSpaces.wordWeight a := by
  classical
  unfold CSSCheckSpaces.wordWeight
  congr 1
  ext i
  simp only [pauliSupport, Finset.mem_filter, Finset.mem_univ, true_and, cssZWord]
  by_cases h : a i = 0 <;> simp [h]

#print axioms cssX_commutation
#print axioms cssZ_commutation
#print axioms cssZWord_support_card

end CriticalDepth.Manuscript20261114.CSSCode
