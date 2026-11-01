import CriticalDepth.TheoremOne
import CriticalDepth.TheoremTwoReduction
import CriticalDepth.CircuitNormalization
import CriticalDepth.BudgetSemantics

/-!
# Closed manuscript targets

These declarations discharge the named reductions with the actual Theorem 1
proof. The at-most-depth targets also include the arbitrary finite gate-list
normalization and the common total-depth budget used in the manuscript.

This source file is a candidate until its recorded Lean build and recursive
axiom audit succeed; the declaration names alone are not verification evidence.
-/

namespace CriticalDepth.Manuscript

theorem theoremTwo_proved : theoremTwo :=
  theoremTwo_of_theoremOne theoremOne_proved

theorem theoremOneAtMost_proved : theoremOneAtMost :=
  theoremOneAtMost_of_theoremOne theoremOne_proved

theorem theoremTwoAtMost_proved : theoremTwoAtMost :=
  theoremTwoAtMost_of_theoremOne theoremOne_proved

end CriticalDepth.Manuscript
