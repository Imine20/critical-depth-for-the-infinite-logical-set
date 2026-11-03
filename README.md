# Critical depth for the infinite logical set

**Independent clean replay: PASS. Author semantic approval: APPROVED.** This branch publishes the 20261103v2 article, its immutable Lean proof snapshot, and new execution evidence.

The article cites proof commit [411ff86](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/411ff86bd30e423b3bc15267006e7bb3b409506d). The publication commit follows that snapshot on the same branch, release/20261103v2-verified. [RELEASE_BINDING.json](RELEASE_BINDING.json) identifies the final TeX/PDF hashes, the exact replay inputs, and the article's final code-availability citation after replay. Subsequent ordinary branch updates do not change the cited commit.

## Article

Download the [TeX](manuscript/shallow_logical_operators_depth_threshold.tex) or [five-page PDF](manuscript/shallow_logical_operators_depth_threshold.pdf). References are ordered by first citation, the unused Beverland entry is removed, and 17 entries remain. The [approved author input](manuscript/provenance/20261103v2-author-approved-input.tex) is preserved. The [editorial check](docs/20261103v2-editorial-check.json) records the bibliography changes, the separately requested introduction change from qubit stabilizer subspace code to qubit stabilizer code, the availability/Lean-scope paragraph and the clarified Bonet-Monroig attribution. It confirms that the remaining text, theorem statements, formulas and figures are unchanged.

## Reproduce the proof

Follow [the clean replay guide](docs/CLEAN_REPLAY.md), using the full proof commit above and a new workspace. Its script installs a fresh pinned toolchain, clones the public snapshot, downloads the locked public dependency cache, and runs both the main source audit and an independent caller.

Read the [actual report](verification-runs/20261103v2-clean/FINAL_REPORT.md), [execution receipt](verification-runs/20261103v2-clean/VERIFICATION.json), [bootstrap provenance](verification-runs/20261103v2-clean/BOOTSTRAP.json), and [compressed full evidence](verification-runs/20261103v2-clean/evidence.tar.gz). The [version index](VERIFICATION_STATUS.md) distinguishes this run from historical records.

The audit covers 1,268 theorem declarations, 1,749 mathematical constants and 41 registered targets. The independent caller makes three closed theorem calls on two explicit codes, covering both main interfaces. The two main recursive axiom sets are exactly propext, Classical.choice and Quot.sound. All nine dependency checkouts match the committed lock.

## Main results and scope

- CriticalDepth.ReviewV2.nativeTheoremOne_proved establishes finiteness and non-density of exact logical actions within one common total circuit-depth budget under the strict-threshold hypotheses.
- CriticalDepth.ReviewV2.standardTheoremTwo_proved establishes the critical-depth equality and a nontrivial closed Circle-isomorphic subgroup for standard qubit stabilizer codes of actual distance d.

[Lean scope and citation note](docs/LEAN_SCOPE_AND_CITATION_NOTE.md), [aligned statements](mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md), [current correspondence](docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md), and [author approval](AUTHOR_SEMANTIC_APPROVAL.json) describe the semantic scope. The independent algebraic proof route is accepted. No line-by-line formalization of the manuscript CAD appendix is claimed.

Lean is 4.35.0, compiler eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Mathlib is 56a005855ea17e0b0958f73ec801ae140b0a1679. The compiler, runtime and pinned public dependency caches remain trusted; the new run rebuilt the project and caller, not every public dependency from source.

[Retained historical notes](docs/HISTORICAL_STATUS_NOTES.md) explain old PENDING/deferred wording in development documents. Earlier receipts, the original approval record and [archived evidence](archive/README.md) retain their historical bytes and scope.
