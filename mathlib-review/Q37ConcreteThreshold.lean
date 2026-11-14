import Q37Threshold
import Q37NamedRotation
import Q37CanonicalDistance
import Q37LogicalNativeGates
import CliffordTNativeThreshold

/-!
# The three arity-three thresholds of the concrete Q37 code
-/

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114.CSSCode
open CriticalDepth.Manuscript20261114.CliffordT
open CriticalDepth.Manuscript20261114 CriticalDepth.Manuscript20261114.Q37Threshold
open scoped ENat

theorem q37LogicalZ_pauli_weight : (pauliSupport (cssZWord q37LogicalZ)).card = 7 :=
  (cssZWord_support_card q37LogicalZ).trans q37LogicalZ_weight

set_option maxRecDepth 4096 in
/-- The verified depth-one partition for each of the two specified
logical gates gives density of finite words. -/
theorem q37CanonicalCode_depth_one_dense :
    (generatedLogicalSubgroup (n := 37) (K := 2) (g := 1) (dim := fun _ => 2)
      q37CanonicalCode.encoding 3 1).topologicalClosure = ⊤ :=
  native_depth_one_dense_of_D_B (n := 37) (g := 1) (dim := fun _ => 2)
    q37CanonicalCode 3 q37_projectiveD_mem_depth_one q37_projectiveB_mem_depth_one

set_option maxRecDepth 4096 in
/-- The five-word Hadamard conjugates the named three-layer Z family
to the X family. Exact one-qubit synthesis then follows by Euler angles. -/
theorem q37CanonicalCode_exact_upper_of_named_rotation :
    nativeExactDepth (n := 37) (K := 2) (g := 1) (dim := fun _ => 2)
      q37CanonicalCode.encoding 3 ≤ 3 :=
  nativeExactDepth_le_of_D_B_Z (n := 37) (g := 1) (dim := fun _ => 2)
    q37CanonicalCode 3 3 (by decide)
    q37_projectiveD_mem_depth_one q37_projectiveB_mem_depth_one
    q37_namedZRotation_mem_depth_three

set_option maxRecDepth 4096 in
theorem q37CanonicalCode_thresholds :
    nativeDenseDepth q37CanonicalCode.encoding 3 = 1 ∧
      nativeCriticalDepth q37CanonicalCode.encoding 3 = 3 ∧
      nativeExactDepth q37CanonicalCode.encoding 3 = 3 := by
  obtain ⟨hdense,hcont,_⟩ := q37Threshold_one_three_three
    q37CanonicalCode q37CanonicalCode_actualDistance
    (cssZWord q37LogicalZ) q37LogicalZ_pauli_weight q37CanonicalCode_logicalZ
    q37CanonicalCode_depth_one_dense
  exact ⟨hdense,hcont,le_antisymm q37CanonicalCode_exact_upper_of_named_rotation
    (q37Threshold_exact_lower q37CanonicalCode q37CanonicalCode_actualDistance
      (cssZWord q37LogicalZ) q37LogicalZ_pauli_weight q37CanonicalCode_logicalZ)⟩

#print axioms q37LogicalZ_pauli_weight
#print axioms q37CanonicalCode_depth_one_dense
#print axioms q37CanonicalCode_exact_upper_of_named_rotation
#print axioms q37CanonicalCode_thresholds

end CriticalDepth.Q37BinaryData