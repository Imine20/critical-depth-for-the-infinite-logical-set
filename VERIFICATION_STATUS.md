# Verification versions and evidence scope

## Algebraic-proof revision

The current branch is revision/20261103v2-algebraic. Its article presents the algebraic proof used by the existing Lean development. Both main theorem statements and the stabilizer proof are unchanged. The new component-count inequality, Bezout estimate and exact-counting discussion appear in End Matter and are not formalized.

The article cites proof-and-scope snapshot ad6a378f6080ba32d92e7c31b6cf71b07685970a. The unchanged Lean source SHA-256 is 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2. The final article hashes and source/evidence bindings are in [RELEASE_BINDING.json](RELEASE_BINDING.json); its [article check](docs/20261103v2-algebraic-check.json) records compilation, reference checks and visual review. No new Lean run is claimed.

## Existing source replay

The [clean replay receipt](verification-runs/20261103v2-clean/VERIFICATION.json) and [report](verification-runs/20261103v2-clean/FINAL_REPORT.md) bind the original proof snapshot 411ff86bd30e423b3bc15267006e7bb3b409506d. They record compilation and recursive axiom checks of the exact source still used here, plus the independent caller. No project axioms or sorryAx were admitted; the main theorem dependencies are propext, Classical.choice and Quot.sound. The compiler, runtime and pinned public caches remain trusted; this was not a rebuild of every dependency from source.

Those records also contain the manuscript and documentation hashes used at the time. Revised prose, readable statement introductions and payload manifests are recorded as changed documents, not silently rebound to that execution. The original author approval remains attached to its original input and two main statements.

## Historical records

Previous publication e199f3338e29ba3d8fbda5212f3a865af0b41d3a, the preserved author input, earlier verification runs, approval history and timestamps retain their original bytes and scope. Historical CAD-route comparisons describe earlier manuscripts. Current scope is in [the Lean statement](docs/LEAN_SCOPE_AND_CITATION_NOTE.md).
