import CSSCodeEncoding
import ShorPhysicalChecks
import ShorPhysicalZChecks

/-!
# Pure physical X and Z checks on CSS coset states
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.BinaryPermutationUnitary
open CriticalDepth.ReviewV2.PauliRowAction
open scoped BigOperators

noncomputable section

variable {n : ℕ}

def cssXWord (a : CSSWord n) (i : Fin n) : SinglePauli :=
  if a i = 0 then .I else .X

def cssZWord (a : CSSWord n) (i : Fin n) : SinglePauli :=
  if a i = 0 then .I else .Z

def cssSign (a : CSSBit) : ℂ := if a = 0 then 1 else -1

private theorem cssBit_eq_zero_or_one (a : CSSBit) : a = 0 ∨ a = 1 := by
  decide +revert

private theorem bit_add_one_self : (1 : CSSBit) + 1 = 0 := by decide

theorem cssSign_add (a b : CSSBit) : cssSign (a + b) = cssSign a * cssSign b := by
  rcases cssBit_eq_zero_or_one a with (rfl | rfl) <;>
    rcases cssBit_eq_zero_or_one b with (rfl | rfl) <;>
    simp [cssSign, bit_add_one_self]

theorem cssSign_sum {ι : Type*} (S : Finset ι) (f : ι → CSSBit) :
    cssSign (∑ i ∈ S, f i) = ∏ i ∈ S, cssSign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cssSign]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, cssSign_add, ih]

private theorem cssXFlip (x : QubitBasis n) (a : CSSWord n) :
    binaryWordEquiv n (flipWord (cssXWord a) x) = binaryWordEquiv n x + a := by
  have hb (b : Fin 2) (w : CSSBit) :
      qubitBitEquiv (singleFlip (if w = 0 then .I else .X) b) = qubitBitEquiv b + w := by
    decide +revert
  funext i
  exact hb (x i) (a i)

theorem cssXWord_mulVec (a : CSSWord n) (v : CSSWord n → ℂ) (x : QubitBasis n) :
    (pauliMatrix 0 (cssXWord a)).mulVec (v ∘ binaryWordEquiv n) x = v (binaryWordEquiv n x + a) := by
  classical
  have hc : rowCoefficient (cssXWord a) x = 1 := by
    apply Finset.prod_eq_one
    intro i _
    unfold cssXWord
    split <;> rfl
  simp only [Matrix.mulVec, dotProduct, pauliMatrix_row, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hc, one_mul, Function.comp_apply, cssXFlip]

theorem cssZWord_mulVec (a : CSSWord n) (v : QubitBasis n → ℂ) (x : QubitBasis n) :
    (pauliMatrix 0 (cssZWord a)).mulVec v x = cssSign (dotProduct (binaryWordEquiv n x) a) * v x := by
  classical
  have hc (b : Fin 2) (w : CSSBit) :
      singleCoefficient (if w = 0 then .I else .Z) b = cssSign (qubitBitEquiv b * w) := by
    fin_cases b <;> rcases cssBit_eq_zero_or_one w with (rfl | rfl) <;>
      simp [singleCoefficient, qubitBitEquiv, cssSign]
  have hcoeff : rowCoefficient (cssZWord a) x = cssSign (dotProduct (binaryWordEquiv n x) a) := by
    unfold rowCoefficient dotProduct
    rw [cssSign_sum]
    exact Finset.prod_congr rfl (fun i _ => hc (x i) (a i))
  have hflip : flipWord (cssZWord a) x = x := by
    funext i
    unfold flipWord cssZWord
    split <;> rfl
  simp only [Matrix.mulVec, dotProduct, pauliMatrix_row, ite_mul, zero_mul, hflip]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change rowCoefficient (cssZWord a) x * v x =
    cssSign (dotProduct (binaryWordEquiv n x) a) * v x
  rw [hcoeff]

variable (H J : Submodule CSSBit (CSSWord n))

theorem cssPhysicalX_fixed_iff (v : CSSWord n → ℂ) :
    (∀ a ∈ H, (pauliMatrix 0 (cssXWord a)).mulVec (v ∘ binaryWordEquiv n) =
      v ∘ binaryWordEquiv n) ↔ (∀ a ∈ H, ∀ x, v (x + a) = v x) := by
  constructor
  · intro h a ha x
    obtain ⟨y, rfl⟩ := (binaryWordEquiv n).surjective x
    have hh := congrFun (h a ha) y
    rwa [cssXWord_mulVec] at hh
  · intro h a ha
    funext x
    rw [cssXWord_mulVec]
    exact h a ha _

theorem cssPhysicalZ_fixed_iff (v : CSSWord n → ℂ) :
    (∀ a ∈ J, (pauliMatrix 0 (cssZWord a)).mulVec (v ∘ binaryWordEquiv n) =
      v ∘ binaryWordEquiv n) ↔ (∀ x, x ∉ cssOrthogonal J → v x = 0) := by
  classical
  constructor
  · intro h x hx
    obtain ⟨a, ha, hdot⟩ : ∃ a ∈ J, dotProduct x a ≠ 0 := by
      by_contra hn
      apply hx
      intro a ha
      by_contra hdot
      exact hn ⟨a, ha, hdot⟩
    obtain ⟨y, rfl⟩ := (binaryWordEquiv n).surjective x
    have hh := congrFun (h a ha) y
    rw [cssZWord_mulVec] at hh
    simp only [cssSign, ite_eq_right hdot, Function.comp_apply, neg_one_mul] at hh
    linear_combination (-1 / 2 : ℂ) * hh
  · intro h a ha
    funext x
    rw [cssZWord_mulVec]
    by_cases hx : binaryWordEquiv n x ∈ cssOrthogonal J
    · have hdot := (cssOrthogonal_mem J _).mp hx a ha
      simp [cssSign, hdot]
    · simp [Function.comp_apply, h _ hx]

#print axioms cssPhysicalX_fixed_iff
#print axioms cssPhysicalZ_fixed_iff

end

end CriticalDepth.Manuscript20261114.CSSCode
