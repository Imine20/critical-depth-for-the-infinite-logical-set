import CSSCodeNormalizerAction
import CSSMonomialCosets

/-!
Connecting the actual physical code range to binary CSS coset ranges.
-/

namespace CriticalDepth.Manuscript20261114.CSSCode

open CriticalDepth.Manuscript CriticalDepth.FaultShorSaturation
open CriticalDepth.Manuscript20261114.CSSCheckSpaces
open scoped Kronecker

variable {n : ℕ}

theorem binaryMonomial_implements_preserves_cosets
    (H J : Submodule CSSBit (CSSWord n)) (hHJ : H ≤ cssOrthogonal J)
    {U : Operator (QubitBasis n)} {f : Equiv.Perm (CSSWord n)}
    {u : CSSWord n → ℂˣ} (hm : binaryMonomial U f u)
    {W : Operator (Fin (2 ^ cssLogicalQubits H J))}
    (hU : Implements (physicalCSSCode H J hHJ) U W) :
    (∀ a ∈ H, ∀ x ∈ cssOrthogonal J, f (x + a) + f x ∈ H) ∧
    ∀ a ∈ H, ∀ x ∈ cssOrthogonal J, u (x + a) = u x := by
  apply binaryMonomial_preserves_cssWordCosets H (cssOrthogonal J) hHJ hm
  intro v hvX hvZ
  let v' : CSSWord n → ℂ := v ∘ (binaryWordEquiv n).symm
  have hIn : v' ∈ cssBinarySpace H J := ⟨hvX, hvZ⟩
  have hOut := cssBinaryAction_mem_space H J hHJ U W hU v' hIn
  have he : v' ∘ binaryWordEquiv n = v := by
    funext x
    exact congrArg v ((binaryWordEquiv n).symm_apply_apply x)
  unfold cssBinaryAction at hOut
  rw [he] at hOut
  exact hOut

#print axioms binaryMonomial_implements_preserves_cosets

end CriticalDepth.Manuscript20261114.CSSCode