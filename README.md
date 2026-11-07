# Critical depth for the infinite logical set

## Latest manuscript

[20261107v7 TeX](manuscript/20261107v7.tex) · [20261107v7 PDF](manuscript/20261107v7.pdf) · [Independent replay and semantic review](verification-runs/20261107v7/REPORT.md) · [Semantic approval (APPROVED)](verification-runs/20261107v7/AUTHOR_SEMANTIC_APPROVAL.json) · [RFC 3161 timestamps](timestamps/20261107v7/README.md)

The v7 files are the exact supplied bytes. The manuscript cites [proof snapshot ad6a378](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/ad6a378f6080ba32d92e7c31b6cf71b07685970a), which has the same Lean proof and dependency lock as this release. See the [input hashes](verification-runs/20261107v7/INPUTS.sha256) for the exact bindings.

## Verify the Lean proof

Use a fresh Linux or WSL checkout with the pinned Lean toolchain and public Mathlib cache.

~~~sh
lake exe cache get
sh scripts/replay.sh
~~~

The [replay entry](scripts/replay.sh) compiles the [integrated proof](mathlib-review/CriticalDepthMathlib.lean), checks its recursive axiom audit and compiles the [separate caller](mathlib-review/SourceConsumer.lean) against the fresh proof artifact. Set CRITICAL_DEPTH_KERNEL_REPLAY=1 for a second check of the two compiled modules with Lean's bundled checker. See the [verification guide](docs/VERIFICATION.md) for resource isolation, the exact commands and the trusted dependency boundary.

| Input | Pin |
| --- | --- |
| Lean | 4.35.0, compiler commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc |
| Mathlib | 56a005855ea17e0b0958f73ec801ae140b0a1679 |
| Transitive public packages | [lake-manifest.json](lake-manifest.json) |

## What the proofs cover

- CriticalDepth.ReviewV2.nativeTheoremOne_proved gives finiteness and non-density of the exact projective logical image under one total-depth budget.
- CriticalDepth.ReviewV2.standardTheoremTwo_proved gives the positive critical depth and a nontrivial closed circle subgroup for ordinary qubit stabilizer subspace codes of actual distance $`d \ge 2`$.
- CriticalDepth.evaluation_image_finite_of_minimalPrime_derivations is the finite-image criterion underlying Theorem 1.

The [readable statements](docs/math/ALIGNED_MATHEMATICAL_STATEMENTS.md), [stabilizer definition correspondence](docs/math/STABILIZER_DEFINITION_CORRESPONDENCE.md) and [original mathematical statements](docs/math/ORIGINAL_PURE_MATHEMATICAL_STATEMENTS.md) have GitHub reading editions with rendered equations.

The [v7 review](verification-runs/20261107v7/REPORT.md) identifies the exact audit inputs and distinguishes theorem-level correspondence from the abstract's scope wording, the alternative coordinate presentation and the unformalized quantitative and fault-tolerance discussion.

## Previous versions

The [version index](VERIFICATION_STATUS.md) separates the v7 evidence from the historical records. The [20261103v2 algebraic revision](RELEASE_BINDING.json) and its [earlier source replay](verification-runs/20261103v2-clean/FINAL_REPORT.md) remain in this branch. The [20261104v1 TeX and timestamp](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/38bc10f39e085099f76b38cf200215aa0208fd61/timestamps/20261104v1) remain available on the earlier main snapshot. The [archive](archive/README.md) retains the preceding records.
