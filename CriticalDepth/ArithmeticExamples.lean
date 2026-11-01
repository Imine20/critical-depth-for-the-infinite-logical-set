import CriticalDepth.Arithmetic

/-! Real calls of arithmetic dependencies, not examples of quantum codes. -/

namespace CriticalDepth.ArithmeticExamples

open CriticalDepth.Arithmetic

theorem binary_distance_eight_depth_four : 4 < criticalDepth 2 8 := by
  apply (below_threshold_iff 2 8 4 (by decide)).mpr
  decide

theorem binary_distance_eight_depth_five : ¬ 5 < criticalDepth 2 8 := by
  intro h
  have hp := (below_threshold_iff 2 8 5 (by decide)).mp h
  have hn : ¬ 2 ^ ceilHalf 5 < 8 := by decide
  exact hn hp

theorem ternary_distance_eight_compression : compressedWeight 3 8 1 = 3 := by
  decide

theorem binary_distance_eight_compression_bound :
    compressedWeight 2 8 (Nat.clog 2 8 - 1) ≤ 2 := by
  exact compressedWeight_at_clog_pred_le 2 8 (by decide) (by decide)

theorem middle_layer_call : min 3 (4 - 3 + 1) ≤ ceilHalf 4 := by
  exact layer_min_le_ceilHalf 4 3 (by decide) (by decide)

theorem synthesis_call :
    (Nat.clog 3 8 - 1) + 1 + (Nat.clog 3 8 - 1) = criticalDepth 3 8 := by
  exact synthesis_depth_at_clog 3 8 (by decide) (by decide)

theorem logarithm_bridge_call :
    Nat.clog 3 8 = ⌈Real.log (8 : ℝ) / Real.log (3 : ℝ)⌉₊ := by
  exact clog_eq_natCeil_log 3 8

theorem unary_at_depth_one_thousand : (1 : ℕ) ^ ceilHalf 1000 < 2 := by
  exact unary_cone_bound 2 1000 (by decide)

theorem arity_at_least_distance_call : Nat.clog 8 8 = 1 := by
  exact clog_eq_one_of_distance_le_arity 8 8 (by decide) (by decide) (by decide)

#print CriticalDepth.Arithmetic.below_threshold_iff
#print CriticalDepth.Arithmetic.compressedWeight_at_clog_pred_le
#print CriticalDepth.Arithmetic.ceilDiv_le_iff
#print axioms CriticalDepth.Arithmetic.below_threshold_iff
#print axioms CriticalDepth.Arithmetic.clog_eq_natCeil_log
#print axioms CriticalDepth.Arithmetic.below_threshold_log_iff
#print axioms CriticalDepth.Arithmetic.layer_min_le_ceilHalf
#print axioms CriticalDepth.Arithmetic.unary_cone_bound
#print axioms CriticalDepth.Arithmetic.ceilDiv_comp
#print axioms CriticalDepth.Arithmetic.ceilDiv_le_iff
#print axioms CriticalDepth.Arithmetic.compressedWeight_eq_ceilDiv_pow
#print axioms CriticalDepth.Arithmetic.compressedWeight_at_clog_pred_le
#print axioms CriticalDepth.Arithmetic.clog_eq_one_of_distance_le_arity
#print axioms CriticalDepth.Arithmetic.synthesis_depth_at_clog
#print axioms CriticalDepth.ArithmeticExamples.binary_distance_eight_depth_four
#print axioms CriticalDepth.ArithmeticExamples.binary_distance_eight_depth_five
#print axioms CriticalDepth.ArithmeticExamples.binary_distance_eight_compression_bound
#print axioms CriticalDepth.ArithmeticExamples.middle_layer_call
#print axioms CriticalDepth.ArithmeticExamples.synthesis_call
#print axioms CriticalDepth.ArithmeticExamples.logarithm_bridge_call
#print axioms CriticalDepth.ArithmeticExamples.unary_at_depth_one_thousand
#print axioms CriticalDepth.ArithmeticExamples.arity_at_least_distance_call

end CriticalDepth.ArithmeticExamples
