# Verification versions and evidence scope

## 20261115 timestamp refresh (current)

The [current version record](CURRENT_VERSION.json) links the [new RFC 3161 evidence](timestamps/20261115-current/README.md) for the current TeX and a deterministic publication-input manifest. The manifest also binds the PDF, mathematical statements, correspondence, corrected historical entry points and existing proof evidence. The timestamp receipt and the manifest have separate roles: the signed tokens bind their input hashes, while the version record and enclosing Git commit bind the complete evidence package.

The two historical entry points now identify the immutable pre-alignment manuscript at `dc1f6d7de3c9435be66c841095650f3bdb0ed72a`. The old tokens and 360-entry input manifest retain their original bytes. Comparing that old manifest requires the old commit's tree, including its original release record.

No mathematical text, Lean source, dependency pin or proof replay result changed in this refresh. The 346-module / 19-audit execution below is reused with exact input-byte checks; this publication does not claim another Lean run. The current timestamp instructions include request, file, chain and revocation verification. OpenTimestamps remains suspended at the author's request.

## 20261115 semantic alignment

The [current version record](CURRENT_VERSION.json) binds the revised manuscript, [complete mathematical statements](docs/math/CURRENT_MATHEMATICAL_STATEMENTS.md), [three-layer correspondence](docs/CURRENT_THREE_LAYER_CORRESPONDENCE.md), and [new full replay](verification-runs/20261115-semantic-alignment/REPLAY.json). The [report](verification-runs/20261115-semantic-alignment/REPORT.md) states the observed results and trust boundary. The Lean proof bytes and mathematical conclusions are unchanged. Only the two background/noise conventions and the availability reference change in the manuscript.

Historical author approvals are not approvals of this newly extracted specification. At the [semantic-alignment publication](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/0f0212793b7a911471d9318f554c8c2a9e41fb1a/CURRENT_VERSION.json), no new timestamp was asserted; the timestamp refresh above adds separate evidence for the current files.

## Update_branch publication before semantic alignment

The earlier release pairs the [manuscript at publication](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/dc1f6d7de3c9435be66c841095650f3bdb0ed72a/manuscript/Update_branch.tex) with the [proof and evidence record](verification-runs/update-branch/RELEASE.md). The recorded full-source replay compiled 346 project modules and passed 19 recursive audit checks for Lean proof commit `e22fb613f4463e0da04c1b0d6c2ea20eacf80c61`. The [RFC 3161 evidence](timestamps/update-branch/README.md) binds the release manuscript and the release input manifest. Earlier builds, manuscript hashes and author approvals retain their original scope.


## 20261107v7

This historical publication contains the exact [v7 TeX](manuscript/20261107v7.tex) and [PDF](manuscript/20261107v7.pdf). The [independent report](verification-runs/20261107v7/REPORT.md) and [execution receipt](verification-runs/20261107v7/REPLAY.json) record the fresh source audit, separate caller and bundled kernel replay.

The [v7 author semantic approval](verification-runs/20261107v7/AUTHOR_SEMANTIC_APPROVAL.json) records **APPROVED** for the reviewed correspondence. The report preserves the status at the time of replay.

## Historical 20261103v2 algebraic-proof revision

The earlier 20261103v2 article presents the algebraic proof used by the existing Lean development. Both main theorem statements and the stabilizer proof are unchanged. The new component-count inequality, Bezout estimate and exact-counting discussion appear in End Matter and are not formalized.

The article cites proof-and-scope snapshot ad6a378f6080ba32d92e7c31b6cf71b07685970a. The unchanged Lean source SHA-256 is 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2. The final article hashes and source/evidence bindings are in [RELEASE_BINDING.json](RELEASE_BINDING.json); its [article check](docs/20261103v2-algebraic-check.json) records compilation, reference checks and visual review. No new Lean run is claimed.

## Existing source replay

The [clean replay receipt](verification-runs/20261103v2-clean/VERIFICATION.json) and [report](verification-runs/20261103v2-clean/FINAL_REPORT.md) bind the original proof snapshot 411ff86bd30e423b3bc15267006e7bb3b409506d. They record compilation and recursive axiom checks of the exact source still used here, plus the independent caller. No project axioms or sorryAx were admitted; the main theorem dependencies are propext, Classical.choice and Quot.sound. The compiler, runtime and pinned public caches remain trusted; this was not a rebuild of every dependency from source.

Those records also contain the manuscript and documentation hashes used at the time. Revised prose, readable statement introductions and payload manifests are recorded as changed documents, not silently rebound to that execution. The original author approval remains attached to its original input and two main statements.

## Historical records

Previous publication e199f3338e29ba3d8fbda5212f3a865af0b41d3a, the preserved author input, earlier verification runs, approval history and timestamps retain their original bytes and scope. Historical CAD-route comparisons describe earlier manuscripts. Current scope is in [the three-layer correspondence](docs/CURRENT_THREE_LAYER_CORRESPONDENCE.md).
