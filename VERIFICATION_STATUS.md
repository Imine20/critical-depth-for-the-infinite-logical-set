# Verification versions and evidence scope

## Current publication

**Fresh independent replay: PASS. Author semantic approval: APPROVED.**

| Object | Identification |
| --- | --- |
| Release branch | release/20261103v2-verified |
| Immutable proof snapshot | 411ff86bd30e423b3bc15267006e7bb3b409506d |
| Final article TeX SHA-256 | 672d39cd821058fe7a18e1079dac69167e982b831e53ce4e0123b0bd1c0521e6 |
| Final article PDF SHA-256 | 35772dffc0f66ff2b81aa31201f1c0ba2d519463f1485f4674face79c53ee4e2 |
| Approved input SHA-256 | 285ad9c537ad494418c250a6be1964476af1e6cd43b331a68733643a54d33ec2 |
| Lean source SHA-256 | 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2 |
| Readable statements SHA-256 | 47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892 |
| Independent caller SHA-256 | 14556a208ecf58045e5124c836e2e1bf662a46292d8856674b728a26f7cc25d5 |

The [new execution report](verification-runs/20261103v2-clean/FINAL_REPORT.md) and [receipt](verification-runs/20261103v2-clean/VERIFICATION.json) record actual compilation and recursive axiom audit of the main source, followed by the independent caller using that newly produced module. [Bootstrap provenance](verification-runs/20261103v2-clean/BOOTSTRAP.json) records the fourth attempt in a new native-ext4 workspace under Ubuntu 24.04 / WSL2, with a fresh toolchain, checkout and public-cache download. The earlier TLS failure (exit 128), missing-Cli rejection (exit 2), and intentional precompilation hashing interruption on 9p/DrvFS (exit 143) remain separately recorded; none reached project compilation. The locked Cli library was compiled from source with build caching disabled; the other public dependencies use the downloaded pinned cache.

The audit passed all 1,749 mathematical constants / 1,268 theorem declarations, 41 targets / 29 exact-three targets, 13 named guards and 12 foundation-origin checks. Own axioms, imported project modules and unapproved imports are all zero. The consumer passed three closed calls and two imported main theorems, with five exact-three checks. All nine dependency Git revisions and tracked sources match the lock. The two main theorem axiom sets are exactly propext, Classical.choice and Quot.sound.

The [release binding](RELEASE_BINDING.json) separates the replay-reference manuscript from the final article. The final availability paragraph differs from the replay reference only in its commit URL and short identifier. The requested introduction wording, explicit Lean scope and clarified Bonet-Monroig attribution already belong to the replay-reference manuscript. All other receipt-bound inputs are unchanged. The publication commit is a descendant on the same branch and is identified by Git itself, avoiding a self-referential embedded hash.

The user approved the main-theorem semantics on 2026-11-03, as recorded in [AUTHOR_SEMANTIC_APPROVAL.json](AUTHOR_SEMANTIC_APPROVAL.json). The algebraic route is accepted; CAD line-by-line formalization is outside this release's scope. Approval, static correspondence, compilation and dependency trust remain separate claims.

## Historical evidence

The [20261102 report](verification-runs/20261102-3c90628/FINAL_VERIFICATION_REPORT.md), its JSON receipt, kernel inventory, reference manuscript and BUILD_INPUTS are unchanged. They retain their earlier manuscript, resource qualifications and execution scope.

The [earlier PENDING approval](archive/approval-history/20261102-pending.json) is preserved byte for byte. The [historical-status ledger](docs/HISTORICAL_STATUS_NOTES.md) explains retained development notes. Earlier timestamps still attest only their named historical bytes. The optional historical dependency-source rebuild remains distinct from this fresh cache-based replay.
