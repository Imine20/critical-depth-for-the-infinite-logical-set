# Verification versions and evidence scope

## Current release

**Mathematical Lean verification: PASS. Author semantic approval: PENDING.**
The user explicitly retained PENDING. CAD formalization is deferred. The selected dependency policy trusts pinned Mathlib/public dependency caches; no Mathlib source tree is vendored.

The current root has one default proof target, CriticalDepthMathlib, from [the integrated source](mathlib-review/CriticalDepthMathlib.lean). The [verification guide](docs/VERIFICATION.md) gives independent build and caller commands.

| Current object | SHA-256 |
| --- | --- |
| Lean source F | 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2 |
| Readable statements S | 47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892 |
| Latest user-provided TeX M1 | 1c17ca04507174ce6b070af71a898626e279668d598d04b8b052787481d9ba0d |
| Latest user-provided PDF | 582ca90c612a57e2e9fdfa67081ab661c7b547178ed66e7be02d75c7cca347e1 |
| Actual replay-reference TeX M0 | 98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227 |
| External caller | 14556a208ecf58045e5124c836e2e1bf662a46292d8856674b728a26f7cc25d5 |

Versions: Lean 4.35.0, compiler eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. All transitive public revisions are in the root [lock file](lake-manifest.json).

## Actual accepted execution

The accepted main compilation ran from 2026-11-01 16:47:05 UTC to 16:53:12 UTC. The separate caller ran from 16:55:54 UTC to 16:56:04 UTC. Their complete input/output bindings were accepted by the evidence validator at 17:01:55 UTC.

| Check | Actual result |
| --- | --- |
| Integrated Main compilation and export | PASS, exit 0 |
| Recursive mathematical inventory | PASS, 1,268 theorem declarations / 1,749 mathematical constants |
| Target registry | PASS, 41 targets / 29 exact-three / 13 named guards / 12 foundation origins |
| Own axioms/project imports/unapproved imports | 0 / 0 / 0 |
| External actual caller | PASS, exit 0, 3 closed calls and 2 imported mains, 5 exact-three checks |
| Two main recursive axiom sets | Exactly propext, Classical.choice, Quot.sound |
| Resource configuration/accounting | Qualified result, described below |
| Author semantic approval | PENDING by explicit user response |
| Original CAD proof line-by-line formalization | DEFERRED by user |

Read the [final report](verification-runs/20261102-3c90628/FINAL_VERIFICATION_REPORT.md), [compact actual execution record](verification-runs/20261102-3c90628/VERIFICATION.json), and [complete types/axiom inventory](verification-runs/20261102-3c90628/KERNEL_AUDIT.txt). The native theorem-two interface is also checked for exactly the same three axioms.

The first integrated attempt compiled successfully but its outer verifier rejected a predicted counter that was one generated helper too high. The merged file shares NativeTheoremTwo._proof_1 instead of emitting a second StandardTheoremTwo._proof_1. The corrected whole verifier then passed. A first external caller attempt failed parameter inference and was rejected for recovery sorryAx; explicit n = 4, k = 2 corrected the caller, and only that caller was rerun. Those rejected attempts are not current acceptance.

## Latest manuscript versus replay-reference manuscript

The actual execution record remains bound to M0 and S/F. The subsequently supplied [latest TeX](manuscript/shallow_logical_operators_depth_threshold.tex) and [latest PDF](manuscript/shallow_logical_operators_depth_threshold.pdf) are copied without edits. Their hash is not substituted into the older execution receipt.

The [latest-manuscript correspondence](docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md) has status STATIC_MATCH_TWO_MAIN_RESULTS_UNDER_STANDARD_SUBSPACE_READING. Paper rho corresponds to Lean q. Theorem 1 matches. Theorem 2 matches for the ordinary [[n,k,d]] stabilizer subspace code, gauge dimension one. The latest text removes the earlier explicit subspace/g=1 wording; this precision issue is listed. No nontrivial-gauge extension or new universality/threshold/37-qubit discussion claim is certified.

The [release binding](verification-runs/20261102-3c90628/RELEASE_BINDING.json) connects these versions. [REFERENCE_MANUSCRIPT.tex](verification-runs/20261102-3c90628/REFERENCE_MANUSCRIPT.tex) and the exact [BUILD_INPUTS](verification-runs/20261102-3c90628/BUILD_INPUTS/) preserve the original run inputs. Later explanatory documentation changes are separated from unchanged mathematical source. The readable statements and named proposition guards are not additional independent proofs or author attestations.

The [approval record](AUTHOR_SEMANTIC_APPROVAL.json) and [review packet](AUTHOR_REVIEW_PACKET.md) remain PENDING. No author role, identity or approval is inferred from a GitHub account.

## Resource qualification

The isolated tool-group memory.max was set to 8,000,000,000 bytes, swap 0, with zero OOM/OOM-kill events. The shared lifetime memory.peak was 8,000,004,096 bytes, already present before both accepted jobs and unchanged afterward: a recorded historical excess of 4,096 bytes. Accepted-job sampling peaks were 7,536,156,672 and 5,684,019,200 bytes at 0.2-second intervals.

[Linux documents](https://docs.kernel.org/admin-guide/cgroup-v2.html#memory-interface-files) temporary usage above memory.max. An unchanged historical peak can be revisited and samples can miss spikes. This is an enforced-configuration/accounting result, not a claim every instantaneous charge throughout the task stayed at most 8 GB. The exact excess cause/duration is not established by these counters. Cloud model services and the desktop controller are outside the user-approved isolated-tool scope.

## History and timestamps

The [archive](archive/README.md) preserves the complete preceding main 5c602e32c66547a183f555e8c963e4621709fc90 as an unchanged child tree. Its source, receipts, manifests and timestamp collections keep their original byte identities and relative paths.

The 47-module development is historical and tied to manuscript 18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85. Its 52-match/one-manuscript-mismatch comparison remains an as-of result, not a new comparison against this current root. The preceding integrated source 85af30d2f9cdf217a729c004d7af0ad67f87b4a821eb28e38ae70dfec840dfd8 and its prior successful runs remain historical evidence.

The optional dependency-source rebuild stopped at the user's request after 3,343/3,699 planned modules. Its temporary source/output copies were deleted, retaining records and the trusted dependency cache. No full dependency-source rebuild is claimed or required.

The [new timestamp record](timestamps/20261102-current/README.md) identifies the exact current collection and separate RFC 3161/OTS results. Old signatures apply only to their named historical bytes.
