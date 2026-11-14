import CSSCodeOrthogonality
import CSSPermutationRigidity

/-!
Mathematical hypotheses on the check spaces in the shallow rigidity lemma.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open CriticalDepth.Manuscript20261114.CSSCode
open scoped Matrix

structure RigidityCheckSpaces {n : ℕ} (H J : Submodule CSSBit (CSSWord n)) (R : ℕ) : Prop where
  compatible : H ≤ cssOrthogonal J
  xDimension : 1 ≤ Module.finrank CSSBit H
  nontrivialLogical : Module.finrank CSSBit H + Module.finrank CSSBit J < n
  xDualDistance : ∀ v ∈ cssOrthogonal H, v ≠ 0 → R + 1 < wordWeight v
  zDualDistance : ∀ v ∈ cssOrthogonal J, v ≠ 0 →
    R * (Module.finrank CSSBit H + 1) < wordWeight v
  zDistance : ∀ v ∈ J, v ≠ 0 →
    max (R * (Module.finrank CSSBit H + 1))
      ((Module.finrank CSSBit J + 1) * (R + 1) + R) < wordWeight v
  linearExclusion : ∀ F : Matrix (Fin n) (Fin n) CSSBit,
    SparseLinearPreserver H R F → F = 1
  symmetricExclusion : ∀ Q : Matrix (Fin n) (Fin n) CSSBit,
    Q.IsSymm → (∀ i, wordWeight (fun j => Q i j) ≤ R + 1) →
      (∀ a ∈ H, Q *ᵥ a ∈ J) → Q = 0

variable {n R : ℕ} {H J : Submodule CSSBit (CSSWord n)}

theorem RigidityCheckSpaces.xDistance (S : RigidityCheckSpaces H J R) :
    ∀ v ∈ H, v ≠ 0 → R * (Module.finrank CSSBit H + 1) < wordWeight v :=
  fun v hv hn => S.zDualDistance v (S.compatible hv) hn

theorem RigidityCheckSpaces.xProjection (S : RigidityCheckSpaces H J R) :
    HasProjection H R := by
  apply hasProjection_of_dualWeightAbove
  intro w hw hdual
  exact (Nat.lt_succ_self _).trans (S.xDualDistance w ((cssOrthogonal_mem H w).mpr hdual) hw)

theorem RigidityCheckSpaces.allowedProjection (S : RigidityCheckSpaces H J R) :
    HasProjection (cssOrthogonal J) (R * (Module.finrank CSSBit H + 1)) := by
  apply hasProjection_of_dualWeightAbove
  intro w hw hdual
  have h : w ∈ cssOrthogonal (cssOrthogonal J) :=
    (cssOrthogonal_mem (cssOrthogonal J) w).mpr hdual
  rw [cssOrthogonal_involutive] at h
  exact (le_max_left _ _).trans_lt (S.zDistance w h hw)

end CriticalDepth.Manuscript20261114.CSSCheckSpaces