import ShorLowerSaturation

open CriticalDepth.Manuscript CriticalDepth.FaultNativeModel CriticalDepth.FaultShorSaturation
open CriticalDepth.FaultHistoryExperimentNormalization
open scoped ENat

-- At depth two, two row groups are necessary when d = 7 and q = 2.
theorem check_shor_depth_two : ∃ C : Code 84 (fun _ => 2) 2 1,
    shorLowerSaturationWitness C 2 7 2 ∧ paperPerCodeExponent C 2 2 = 2 := by
  exact exists_shor_lower_saturation_paperPerCodeExponent 7 2 2
    (by decide) (by decide) (by decide)

-- Depth one and arity three, also with more than one row group.
theorem check_shor_depth_one : ∃ C : Code 84 (fun _ => 2) 2 1, shorLowerSaturationWitness C 3 7 1 := by
  exact exists_shor_lower_saturation 7 3 1 (by decide) (by decide) (by decide)
