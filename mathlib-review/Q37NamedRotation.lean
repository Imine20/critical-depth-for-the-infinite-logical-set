import NamedBareRotation
import Q37PhysicalCompression
import Q37CanonicalLogicalPauli

/-!
# Exact logical rotation from the stated Q37 physical circuit
-/

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.Manuscript20261114 CriticalDepth.Manuscript20261114.CSSCode

theorem q37_namedZRotation_mem_depth_three (t : ℝ) :
    projectiveRotation SinglePauli.Z.matrix (singlePauli_selfAdjoint .Z)
      (singlePauli_sq .Z) t ∈ nativeLogicalImage q37CanonicalCode.encoding 3 3 := by
  obtain ⟨L,hL,hev⟩ := q37Compression_rotation_circuit t
  exact barePauli_projectiveRotation_of_layer_sequence q37CanonicalCode (cssZWord q37LogicalZ)
    SinglePauli.Z.matrix q37CanonicalCode_logicalZ (singlePauli_selfAdjoint .Z)
    (singlePauli_sq .Z) t L hL.le hev

#print axioms q37_namedZRotation_mem_depth_three

end CriticalDepth.Q37BinaryData
