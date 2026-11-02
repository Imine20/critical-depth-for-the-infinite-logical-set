# Verification versions and evidence scope

## Current branch

Author semantic approval: **APPROVED**, recorded from the user's 2026-11-03 instruction and bound to the exact selected input in [AUTHOR_SEMANTIC_APPROVAL.json](AUTHOR_SEMANTIC_APPROVAL.json). It concerns the two main theorem statements and their Lean semantics, with the algebraic proof route accepted. CAD line-by-line formalization is outside this release's scope.

Fresh independent replay: **PREPARED, NOT YET RECORDED** in this proof-snapshot commit. [scripts/clean_replay.sh](scripts/clean_replay.sh) and [scripts/verify_release.sh](scripts/verify_release.sh) provide the entry points. An actual execution receipt must be published separately after this commit exists; this document is not a successful-run receipt.

| Object | SHA-256 |
| --- | --- |
| Approved author input | 285ad9c537ad494418c250a6be1964476af1e6cd43b331a68733643a54d33ec2 |
| Main Lean source | 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2 |
| Readable statements | 47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892 |
| Independent caller | 14556a208ecf58045e5124c836e2e1bf662a46292d8856674b728a26f7cc25d5 |

The main source and caller are unchanged. The new verifier makes the separate caller mandatory, checks dependency Git revisions and binds the fresh main artifacts through the caller run. The [verification guide](docs/VERIFICATION.md) describes its complete scope.

## Historical verification

The [20261102 report](verification-runs/20261102-3c90628/FINAL_VERIFICATION_REPORT.md), [JSON receipt](verification-runs/20261102-3c90628/VERIFICATION.json), [kernel inventory](verification-runs/20261102-3c90628/KERNEL_AUDIT.txt), reference manuscript and BUILD_INPUTS remain unchanged. They record successful main compilation, all 1,749 mathematical constants / 1,268 theorem declarations, 41 targets / 29 exact-three targets, and a separate caller with three closed proofs and two imported mains. The recursive axiom sets of both main theorems are exactly `propext`, `Classical.choice`, `Quot.sound`.

Those receipts describe their own earlier manuscript and execution environment. Their historical resource qualifications, rejected attempts and stopped optional dependency-source rebuild are retained in that report. They are not relabeled as the new independent replay.

The [earlier approval record](archive/approval-history/20261102-pending.json) preserves the previous PENDING decision. The user's new approval supersedes it for the input identified above. [Archived source and timestamp evidence](archive/README.md) still refers only to its named historical bytes.
