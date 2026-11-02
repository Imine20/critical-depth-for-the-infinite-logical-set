# Current manuscript and formal-statement correspondence

**Static correspondence: the two main results match under the ordinary stabilizer subspace-code reading. Semantic approval: APPROVED by the user's explicit instruction on 2026-11-03.**

This document binds the selected input manuscript to the unchanged mathematical Lean source. It is a static statement/definition comparison, not a fresh execution receipt or whole-paper certification. The approval and its scope are recorded in [AUTHOR_SEMANTIC_APPROVAL.json](../AUTHOR_SEMANTIC_APPROVAL.json).

## Exact inputs

| Object | Bytes | SHA-256 |
| --- | ---: | --- |
| Selected TeX input, manuscript/provenance/20261103v2-author-approved-input.tex | 36,732 | 285ad9c537ad494418c250a6be1964476af1e6cd43b331a68733643a54d33ec2 |
| Readable statements, mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md | 11,529 | 47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892 |
| Integrated source, mathlib-review/CriticalDepthMathlib.lean | 543,694 | 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2 |

Manuscript line references below refer to this 817-line input, not to a later publication TeX after editorial or availability updates. TeX labels provide stable statement locators. Final TeX/PDF hashes and the article's cited proof snapshot are recorded separately in the release binding.

The readable statements retain their historical reference manuscript hash and old line numbers. They have not been silently rebound or rewritten. The mapping below is the explicit bridge to the selected input.

## Definitions and main conclusions

"R" below abbreviates "CriticalDepth.ReviewV2". The manuscript's arity rho is the formal parameter q: a bound on the number of physical factors touched by a primitive gate, not a geometric radius.

| Manuscript location | Mathematical content | Formal correspondence |
| --- | --- | --- |
| Lines 72-76 | Finite physical factors, isometric encoding, logical dimension K >= 2 and gauge dimension g >= 1 | Native matrix encoding and the Hilbert-coordinate transport. The arbitrary-carrier theorem preserves the physical tensor factors and their supports. |
| Lines 77-82; eq:correctable | Every complex operator supported on fewer than d factors compresses to I_L tensor M_O | R.NativeDetectsBelow, source line 9924; this is a lower-distance condition, sufficient for Theorem 1. |
| Lines 83-94; eq:encoded | Exact action UV = V(W tensor Z) for all logical and gauge states, counted modulo scalar phase; at most h disjoint-support layers | R.nativeLogicalImage and the gate/layer/circuit predicates; the image permits a number r <= h of layers. R.logical_factor_projective_unique supplies the phase-uniqueness bridge. |
| Lines 205-219; thm:depth and eq:depth | Finiteness and non-density when h < 2 ceil(log_rho d) - 1 | R.NativeTheoremOne, source lines 10002-10007, proved by R.nativeTheoremOne_proved at line 10009. R.HilbertCircuitTransport.theoremOne_arbitrary_carriers at line 11025 supplies the general Hilbert-space presentation. |
| Lines 382-390; eq:critical-definition | First positive depth budget with infinite image, or infinity if none exists | R.nativeCriticalDepth, source line 9984, and the proved legacy/native equality. |
| Lines 478-488; cor:critical | Ordinary [[n,k,d]] qubit stabilizer subspace code, k >= 1, actual d >= 2, q >= 2 | R.StandardStabilizerCode, line 11793; R.NativeActualDistance, line 9930; R.StandardTheoremTwo, lines 11918-11927. |
| Lines 483-487; eq:critical | Critical-depth equality and a nontrivial continuous one-parameter subgroup at that depth | R.standardTheoremTwo_proved, line 11929. Its conclusion includes a closed nontrivial subgroup with a topological group isomorphism from Circle and direct containment in the bounded-depth image. |
| Lines 494-520; eq:pauli-family | A minimum-weight logical Pauli generates the compressed rotation construction, with projective period pi | The constructive stabilizer development and R.critical_circle_joint_witness, line 10167. The weight-d Pauli witness is derived from the stabilizer and actual-distance assumptions. |

Theorem 1 retains n >= 1, K >= 2, g >= 1, d >= 2, rho >= 2, h >= 1, the isometry and detection assumptions, and the strict depth inequality. No intermediate code-preservation, geometry, stabilizer or finite-alphabet condition is added. Theorem 2 retains actual distance, including the failure witness at weight d.

## Stabilizer convention and gauge scope

The input introduction explicitly says "qubit stabilizer subspace code" at lines 64-67. Theorem 2 uses the ordinary [[n,k,d]] stabilizer-code notation. Its intended code is the whole common +1 eigenspace of an abelian Pauli subgroup excluding minus identity, with gauge dimension one. This is the standard interface in Lean.

R.nativeStabilizer_iff_standard, source line 11895, proves the equivalence with the native whole-fixed-space convention under the isometry assumption. The required commutation, exclusion of minus identity and subgroup finiteness are proved. No extension of the sharp equality to nontrivial-gauge subsystem stabilizer codes is asserted.

The formal circuit representation permits empty-support scalar gates. Removing such gates and absorbing their phases into the gauge factor preserves the projective logical image. Their inclusion does not change either main conclusion.

## Independent proof route

The input uses the corrected propagated insertion H_j at lines 270-277. Its finiteness proof then uses a smooth cell and path argument, with the End Matter lemma at lines 680-685. The Lean proof obtains the same finiteness conclusion by an algebraic/derivation route. The user explicitly accepts this difference; CAD-path formalization is outside the selected release scope rather than an unresolved approval condition. See [the route comparison](../mathlib-review/CAD_VS_ALGEBRAIC_PROOF.md).

## Claims outside the two formal interfaces

| Input passage | Coverage limit |
| --- | --- |
| Introduction, lines 49-70 | Literature statements, noise thresholds, space overhead and rhetorical comparisons are not established by the two main formal theorems. |
| Lines 343-380 | A finite bounded-depth logical image need not have a finite or nondense generated group. The specific Dua [[37,1,7]] code and its universal generators are not instantiated by a closed formal proof here. No fault-tolerance protocol or uniform compilation-overhead theorem is claimed. |
| Lines 524-528 | The central-gate fault example clarifies the construction's lack of protection against arbitrary single-gate faults. It is a written observation, not part of the two named formal targets. |
| Figures and End Matter, lines 665-815 | The diagrams, finite smooth-cell construction, root branches and analytic path argument are not certified line by line by the independent algebraic Lean proof. |
| Acknowledgment, funding and code availability | These are publication metadata, not formal mathematical conclusions or evidence of independent identity verification. |

The two theorems establish the onset of an infinite exact logical image and a continuous logical direction. They do not establish a finite-image cardinality bound uniform over code families, full logical addressability, fault-tolerant continuous control, or impossibility of a dense generated gate group.

## Approval and execution records

The current semantic approval supersedes the old PENDING status for the identified input and scope. The old approval file is preserved byte for byte at [archive/approval-history/20261102-pending.json](../archive/approval-history/20261102-pending.json). It remains a valid historical record.

This static correspondence does not relabel the 2026-11-02 execution as a run on the new manuscript. That run's reference input, timestamps and trust qualifications remain unchanged. New execution evidence must identify its own source snapshot, dependency policy and actual commands. Consult [VERIFICATION_STATUS.md](../VERIFICATION_STATUS.md) for the executed status of the new branch.

The publication article and immutable proof snapshot belong to the same release branch. A later publication commit can update the article's availability citation and attach receipts while preserving the proof inputs. Exact final bytes and their relation to the approved input are a release-binding matter, distinct from this statement comparison.
