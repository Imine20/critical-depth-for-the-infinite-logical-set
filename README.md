# Critical depth for the infinite logical set

This branch synchronizes the 20261103v2 article with its Lean proof and a clean-checkout verification entry point. The author has approved the semantics of the two main theorems and accepted the independent algebraic proof route; see the [approval record](AUTHOR_SEMANTIC_APPROVAL.json). The manuscript's CAD proof remains outside the formalization scope.

The integrated proof source is unchanged from the previous verified release. A new independent replay is prepared on this branch; until a new execution receipt is published, the [20261102 run](verification-runs/20261102-3c90628/FINAL_VERIFICATION_REPORT.md) is historical evidence, not a fresh-environment result for this branch.

## Reproduce

Use an immutable commit from this branch and a new empty workspace on Linux x86_64. Follow [the clean replay guide](docs/CLEAN_REPLAY.md). The entry point installs a pinned Lean toolchain in that workspace, clones the public repository, fetches the locked public dependency cache, and runs:

```sh
sh scripts/verify_release.sh
```

Both the integrated proof and [independent caller](mathlib-review/SourceConsumer.lean) must succeed. The caller uses the main module produced in that same run. All nine dependency checkout revisions must match [lake-manifest.json](lake-manifest.json). The [verification guide](docs/VERIFICATION.md) explains the checks and trusted inputs.

## Main results

- `CriticalDepth.ReviewV2.nativeTheoremOne_proved`: finiteness and non-density of exact logical actions within one common total depth budget, below the strict threshold, for the stated finite-dimensional subsystem codes.
- `CriticalDepth.ReviewV2.standardTheoremTwo_proved`: the critical-depth equality and a nontrivial closed Circle-isomorphic subgroup for standard stabilizer subspace codes of actual distance d.

The [aligned statements](mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md) expose the assumptions. The [manuscript correspondence](docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md) separates semantic correspondence from compilation and from the proof route. The Lean proof does not formalize the CAD appendix line by line.

## Article and versions

The current [TeX](manuscript/shallow_logical_operators_depth_threshold.tex) and [PDF](manuscript/shallow_logical_operators_depth_threshold.pdf) order references by first citation and remove the unused Beverland entry. They also incorporate the requested introduction wording, explicit Lean scope and a narrower Bonet-Monroig attribution; see the [scope and citation note](docs/LEAN_SCOPE_AND_CITATION_NOTE.md). The theorem statements and mathematical construction steps are unchanged. The exact [approved input](manuscript/provenance/20261103v2-author-approved-input.tex) is preserved separately.

The final article will cite an immutable proof snapshot on this branch. Its publication commit follows that snapshot and records the article hashes and replay evidence; an article cannot contain its own enclosing Git commit SHA. Moving the branch later does not change the cited snapshot.

Lean is 4.35.0 (compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and eight further locked packages. The proof trusts Lean, its bundled runtime and the pinned public dependency cache. It does not claim a full source rebuild of all dependencies.

The [version index](VERIFICATION_STATUS.md) distinguishes current approval from historical execution records. [Archived evidence](archive/README.md), prior run receipts and existing timestamps retain their original bytes and scope.

The [bootstrap correction record](docs/BOOTSTRAP_CORRECTION_20261103.json) preserves two failed setup attempts. The entry point now builds the locked Cli library missing from Mathlib's cache. A new fresh replay is pending; no successful result is claimed for those attempts.
