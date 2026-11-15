# Critical depth for the infinite logical set

## Current manuscript and Lean proofs

- [Update_branch.tex](manuscript/Update_branch.tex)
- [Manuscript-to-Lean correspondence and replay instructions](verification-runs/update-branch/RELEASE.md)
- [Full-source replay and recursive axiom audit](mathlib-review/CONTINUATION_VERIFICATION.json)
- [RFC 3161 timestamps](timestamps/update-branch/README.md)

The manuscript cites the [immutable Lean proof snapshot e22fb61](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/e22fb613f4463e0da04c1b0d6c2ea20eacf80c61). The snapshot proves finiteness of the bounded-depth logical image, the two logical depth threshold results, both universal fault-suppression bounds and their Shor and CSS saturations. It also gives the first uncorrectable fault order and the three optimal error exponents of a fixed circuit. The full replay compiled 346 project modules and passed 19 audit checks. The audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Reproduce the full project verification

Use a fresh Linux or WSL checkout with the versions pinned in [lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json). From the repository root, run:

~~~sh
lake exe cache get
lake --no-cache build '@Cli/Cli:leanArts'
lake env sh mathlib-review/verify-v3.sh /absolute/path/to/new-output
~~~

The [release record](verification-runs/update-branch/RELEASE.md) states the source, dependency and manuscript bindings, and gives the scope of the replay.

## Previous versions

See the [version index](VERIFICATION_STATUS.md) for the historical scope of earlier builds and author approvals. The [20261107v7 TeX](manuscript/20261107v7.tex), [PDF](manuscript/20261107v7.pdf), [review](verification-runs/20261107v7/REPORT.md) and [timestamps](timestamps/20261107v7/README.md) are preserved. The [20261114v0 TeX and timestamp](timestamps/20261114v0/README.md) and the [20261104v1 TeX and timestamp](timestamps/20261104v1/README.md) retain their original bindings. The [algebraic-proof revision](RELEASE_BINDING.json) and [archive](archive/README.md) document the earlier history.
