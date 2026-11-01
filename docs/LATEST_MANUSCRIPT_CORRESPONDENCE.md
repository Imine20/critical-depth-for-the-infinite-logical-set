# Latest manuscript: correspondence with the verified formal statements

**Status: `STATIC_MATCH_TWO_MAIN_RESULTS_UNDER_STANDARD_SUBSPACE_READING`.**
The latest first theorem matches the verified statement after renaming gate
arity `q` to `ρ`. The latest second theorem matches for ordinary `[[n,k,d]]`
qubit stabilizer **subspace** codes, with gauge dimension one. The wording
difference concerning this scope is recorded below. This is an AI/internal
static correspondence review, not author approval or whole-paper validation.
**Author semantic approval remains PENDING.**

All 793 lines of the latest TeX were read, including the definitions and both
theorem statements and proofs. The earlier definitions and main statements,
the unchanged readable statements S, and the relevant declarations in F were
compared. No TeX instruction or author TODO was executed. No Lean, WSL, build,
network, or additional CAD proof audit was run for this comparison.

## Exact versions

| Object | Bytes | SHA-256 |
| --- | --- | --- |
| Latest supplied TeX, M1 | 35,519 | `1c17ca04507174ce6b070af71a898626e279668d598d04b8b052787481d9ba0d` |
| Latest supplied PDF | 414,237 | `582ca90c612a57e2e9fdfa67081ab661c7b547178ed66e7be02d75c7cca347e1` |
| Previous run-reference TeX, M0 | 36,687 | `98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227` |
| Readable statements S | 11,529 | `47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892` |
| Formal source F | 543,694 | `3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2` |
| Existing point-in-time `VERIFICATION.json` | 20,083 | `4d30510ea1f9379120a9187423d43b5bc7e94b1e296076b7ee531bec667da4fa` |

The PDF's exact bytes are identified here; this comparison did not visually
verify its rendering or independently establish its derivation from the TeX.
M0 and M1 were read from separate frozen revision copies. Neither was edited.

## Notation and definition mapping

The code/S parameter `q` is the paper's new integer `ρ`: maximum **number of
physical subsystems per gate**, not a geometric radius. The new
`𝓛≤h(C,ρ)` is the previous `𝓛≤h(C;q)`. Both use one common total budget and
one scalar logical phase. No change to F is needed for this renaming.

Names below beginning `R` mean `CriticalDepth.ReviewV2`; `Manuscript` means
`CriticalDepth.Manuscript`. Formal line locations refer to unchanged F above.

| Definition or conclusion | M0 lines | M1 lines | S/F correspondence and finding |
| --- | --- | --- | --- |
| Finite physical factors; encoding isometry; `K ≥ 2`, `g ≥ 1` | 258–270 | 238–242 | S §1; native raw-matrix isometry or Mathlib arbitrary-carrier linear isometry. Same assumptions. |
| Detection below `d`: every supported complex operator compresses to `I_L ⊗ M_O` | 270–277, `eq:correctable` at 272 | 243–248, label at 245 | S §1; `R.NativeDetectsBelow` F:9924. M1 explicitly calls `d` a distance lower bound, consistent with T1's existing formal premise. |
| Exact implementation `UV=V(W⊗Z)` on every logical/gauge state | 279–285, label at 280 | 249–255, label at 250 | S §2; equation inside `R.nativeLogicalImage`, F:9767. `R.logical_factor_projective_unique` supplies the phase-uniqueness bridge. |
| At-most total depth, disjoint supports within layers, arbitrary supports/unitaries | 287–294 and 425–429 | 256–260, 287–293 | S §2; `NativeGateAllowed`, `NativeLayerAllowed`, `NativeCircuitAllowed`, F:9725; image quantifier `∃ r ≤ h`, F:9770. Definition moved before T1 without changing its scope. |
| First theorem: finite logical image and nondensity below the strict threshold | 296–308; threshold label 300 | 280–294; threshold label 284 | S §3; `R.nativeTheoremOne_proved : NativeTheoremOne`, F:10002–10015, and `R.HilbertCircuitTransport.theoremOne_arbitrary_carriers`, F:11025. Same conclusion and bounds after `q=ρ`. |
| First positive budget with infinite image; infinity if none | 425–440; definition label 431 | 451–461; definition label 452 | S §4; `R.nativeCriticalDepth`, F:9984. The minimum still uses `h ≥ 1`; circuits inside a positive budget may have length zero. |
| Actual-distance ordinary qubit stabilizer code, `k ≥ 1`, arity at least two | 442–452 | 476–486 | S §4 and standard supplement; `R.StandardStabilizerCode` and `R.NativeActualDistance`. Match uses the standard subspace reading explained below. |
| Critical equality `h∞ = 2⌈log_ρ d⌉−1` and nontrivial continuous subgroup | 447–451 | 481–485 | `R.standardTheoremTwo_proved : StandardTheoremTwo`, F:11918–11932; the original `R.nativeTheoremTwo_proved` remains. No additional theorem, Pauli witness, or desired conclusion is a premise. |
| Pauli rotation family; projective period `π`; nontrivial `U(1)` subgroup | 475–483; family label 476 | 509–517; family label 510 | S §5; `R.critical_circle_joint_witness`, F:10167. The formal conclusion retains a closed Circle-isomorphic subgroup and membership for every angle, which is stronger than the main statement. |

For T1, all material bounds are retained: `n ≥ 1`, `K ≥ 2`, `g ≥ 1`,
`d ≥ 2`, `ρ ≥ 2`, `h ≥ 1`, isometry, detection below `d`, and the strict
depth inequality. There is no new stabilizer, geometry, finite gate alphabet,
or intermediate code-preservation assumption. Actual distance is required
for T2 and is not weakened to detection alone.

## Scope precision for the second theorem

M0 explicitly said “stabilizer subspace code” and explained that a subspace
code has `g=1`. M1 says “`[[n,k,d]]` qubit stabilizer code” at line 477 and
removes the earlier subspace/gauge-dimension explanation. Under the usual
ordinary stabilizer-code convention, its code space is the whole common +1
eigenspace of an abelian Pauli subgroup excluding minus identity, has logical
dimension `2^k`, and uses `g=1`. That is exactly the standard-code interface in
F and S, with its proved native/standard equivalence and derived finiteness.

This wording change is a precision difference. The correspondence does **not**
infer an extension to subsystem stabilizer codes with `g>1`. Such an extension
is not the theorem proved in F. Restating “subspace” or `g=1` would make the
scope explicit, but the supplied manuscript is preserved unchanged and no
further approval is requested. Author review of this interpretation remains
PENDING.

M1 also removes the explicit empty-support phase explanation from M0.
F already allows empty-support gates and proves that their scalar phases can
be absorbed into the gauge factor without changing the projective image.
Thus their inclusion or removal does not change either counted image. The
normalization's nonempty physical basis follows from the existing isometry
and positive logical/gauge dimensions; it is not an extra premise.

## Changes outside the two verified main statements

The new article is more than a layout revision. The following distinctions
must accompany any statement about verification coverage:

| Latest passage | Coverage and limit |
| --- | --- |
| Introduction, lines 53–64: error spread and a cited fault-tolerance threshold/constant-space construction | These are fault-tolerance and literature claims. F's locality bounds do not supply a noise model, decoder, threshold theorem, or overhead theorem. This comparison does not verify those claims. |
| Introduction, lines 80–93: stabilizer codes attain the smallest onset depth at given distance and arity | This is a scoped consequence of the universal lower bound plus ordinary-stabilizer upper bound, within the same exact fixed-code circuit model. It establishes no general superiority in universality, overhead, error thresholds, or existence of codes for every parameter choice. |
| Discussion, lines 412–437: the Dua `[[37,1,7]]` example and the pair `T†`, `√X†` generating a dense subgroup | F does not construct this 37-qubit code, prove those gadget implementations, or prove the pair's universality. Generic T1 applies if the actual encoding/detection hypotheses are supplied externally; this is not a closed formal application to that cited code. The stated numerical threshold is `2⌈log_3 7⌉−1=3`. |
| Discussion, lines 440–449: compilation from a finite shallow alphabet and unbounded word lengths for uniform arbitrary-accuracy control | These are additional compilation/protocol observations. The distinction between finite bounded-budget image and possibly dense generated group is consistent with T1, but F does not provide a formal compilation or fault-tolerance protocol theorem. |
| Removed M0 remarks, lines 486–510 | Their removal does not prove their converses. No full-register universality, subsystem critical-depth equality, intermediate fault tolerance, uniform cardinality bound, or overhead bound follows from the two main formal results. |
| Figure and proof prose; End Matter lemma now at line 650 instead of 692 | The formal proof remains the alternative algebraic/derivation route. The manuscript's CAD smooth-cell/root/path argument remains deferred. No extra CAD correctness review or formal Clifford classification was performed here. |

The methods/literature passages and author revision markers are source
content, not instructions to this reviewer. Bibliographic assertions were not
independently rechecked. The new narrative claims are not silently included
in the formal main-theorem acceptance.

## Relation to the actual verification record

The existing report identifies M0 `98e...`, S `47a...`, and F `3c906...`.
Its actual formal audit records 1,268 theorem declarations, 1,749 mathematical
constants, 41 targets, 29 exact-three targets, 13 named guards, and 12 Mathlib
foundation checks under the explicit trusted-cache dependency policy. This
document neither reruns those checks nor changes the report's original
manuscript hash, timestamps, or point-in-time author-review status.

S likewise remains explicitly bound to M0; its old manuscript line numbers
are not claimed to be current M1 locations. The mapping above is the separate
bridge to M1. It supports referencing the unchanged formal proofs for the two
latest main statements under the stated subspace reading, without claiming
that the earlier run processed M1, validated its new discussion or PDF, or
checked the entire paper. No formal-source change or kernel rerun was
identified as necessary for these two statement correspondences.
