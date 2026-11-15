# Critical depth for the infinite logical set

## Current manuscript, statements and proofs

- Manuscript: [TeX](manuscript/Update_branch.tex) · [PDF](manuscript/Update_branch.pdf)
- [Complete mathematical statements](docs/math/CURRENT_MATHEMATICAL_STATEMENTS.md)
- [Manuscript → statements → Lean correspondence](docs/CURRENT_THREE_LAYER_CORRESPONDENCE.md)
- [Exact version and evidence binding](CURRENT_VERSION.json)
- [Full verification report](verification-runs/20261115-semantic-alignment/REPORT.md)
- [Current RFC 3161 timestamps and verification commands](timestamps/20261115-current/README.md)

The current statements cover the bounded-depth projective logical image, continuous onset, dense and exact generation, the three optimized fault-suppression exponents, both saturation constructions, and the synthesis and code examples. The distinction between one complete circuit's depth and the depth of each generator is explicit.

This revision clarifies the abstract's detectable-partition and global-phase conditions and specifies that noise occurs at nonempty-support gate locations. Nonempty-support identity gates remain noise locations. The mathematical conclusions and all Lean proof sources are unchanged from the [immutable proof snapshot e22fb61](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/e22fb613f4463e0da04c1b0d6c2ea20eacf80c61).

## Reproduce the full verification

Use the versions in [lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json), with Python 3.10 or later available. From the repository root:

~~~sh
lake exe cache get
lake --no-cache build '@Cli/Cli:leanArts'
lake env python scripts/verify_full.py /absolute/path/to/new-output
~~~

Use `python3` if that is the interpreter name on your system. The output directory must not already exist. The runner compiles the complete 346-module manifest and checks all 19 recursive audit markers. It records actual results and input, dependency, log and artifact hashes. The permitted foundational axioms are `propext`, `Classical.choice` and `Quot.sound`. See [the verification guide](docs/VERIFICATION.md) for the trust boundary, native Windows invocation and the original POSIX entry point.

## Version history

[VERIFICATION_STATUS.md](VERIFICATION_STATUS.md) separates the current publication from earlier builds and approvals. The new [RFC 3161 evidence](timestamps/20261115-current/README.md) binds the current TeX directly and the publication inputs through a SHA-256 manifest. [RELEASE_BINDING.json](RELEASE_BINDING.json), the root author-approval record, and the earlier [Update_branch release record](verification-runs/update-branch/RELEASE.md) retain their historical scope. The [earlier timestamps](timestamps/update-branch/README.md) still bind their original manuscript and manifest; their tokens and input manifest are unchanged. No historical approval or timestamp is reassigned to the new statements.
