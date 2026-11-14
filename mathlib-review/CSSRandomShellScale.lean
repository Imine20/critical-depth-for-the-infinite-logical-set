import CSSRandomProbabilityArithmetic
import CSSSparseMatrixCounts

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

theorem css_bound_for_shells (R k : ℕ) (hR : 2 ^ 20 ≤ R)
    (hk : k + 1 ≤ cssSites R) :
    natShells (cssSites R) k ≤ 2 ^ ((R / 256) * (k + 1)) := by
  unfold natShells
  exact natShells_le_power _ _ _ (by unfold cssSites; positivity) (twelve_pow_bound R hR)
    (hk.trans (twelve_pow_bound R hR))

end CriticalDepth.Manuscript20261114.CSSCheckSpaces
