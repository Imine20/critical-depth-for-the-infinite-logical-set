# Verify the current proof

The sole default target is `CriticalDepthMathlib`. Its integrated [source](../mathlib-review/CriticalDepthMathlib.lean) imports public Mathlib modules and Lean audit APIs. No private project proof modules or prebuilt project artifacts are needed.

## Clean environment

Use [CLEAN_REPLAY.md](CLEAN_REPLAY.md) for a fresh toolchain installation, checkout and cache directory. It requires Linux x86_64, Git, curl, Python 3, Perl and standard GNU command-line tools. It does not change HOME or reuse a previous project's .lake directory. No `lake update` is run.

With the locked toolchain and public dependency outputs already installed in a checkout, the complete verification command is:

```sh
sh scripts/verify_release.sh
```

For initial dependency setup, run `lake exe cache get` followed by `lake --no-cache build '@Cli/Cli:leanArts'`. Mathlib's cache omits the locked Cli library; this additional command builds its actual Lean artifacts from source. Keep the committed lock file unchanged. Lean must be 4.35.0, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`; eight other package commits are listed in [lake-manifest.json](../lake-manifest.json).

## Combined entry for a fresh checkout

Clone with byte-preserving settings when preparing the checkout with Windows Git, for example with git -c core.autocrlf=false clone. Run the verifier in Linux or WSL.

~~~sh
lake exe cache get
sh scripts/replay.sh
~~~

The wrapper runs the source audit and the separate caller below in sequence. It requires a fresh output tree so the caller can only use the main artifact produced by the current run. It records and rechecks the hashes of that artifact's generated parts. To rerun in the same checkout, move the previous .verification directory aside first.

For a separate kernel pass after the build and caller, run the wrapper with CRITICAL_DEPTH_KERNEL_REPLAY=1. This uses the bundled leanchecker from the selected toolchain and checks the project modules against the pinned imports. The operating-system resource boundary is supplied by the caller. In the trusted-cache mode described below, the wrapper uses the same explicit compiler and public cache roots as the source verifier.

## Required checks

The release wrapper checks package revisions and compiles the main source through [verify.sh](../scripts/verify.sh). That script allocates a new output directory, validates source/payload bindings and checks dependency artifacts before and after compilation. The embedded audit covers 1,268 theorem declarations and 1,749 own mathematical constants, including private, generated and unused declarations. There are 41 registered targets, 29 exact-three targets, 13 named proposition guards and 12 Mathlib-foundation origin checks. Own mathematical declarations may have no recursive axioms outside:

```text
propext
Classical.choice
Quot.sound
```

The exact-three targets must use all three. The scan includes the audit namespace when rejecting own axioms. Target declared types and transparent weak-head types are printed without ellipses; this is not normalization beneath every binder.

The wrapper then compiles [SourceConsumer.lean](../mathlib-review/SourceConsumer.lean), using only the newly produced project module and the checked public dependency outputs. The three closed calls use explicit five-qubit and four-qubit codes. Together with the two imported main theorems, all five targets must have exactly the three permitted axioms. The main artifacts are checked before and after this caller. Both compilations and the exact expected audit markers must succeed before a release verification receipt reports PASS.

The two main interfaces are `CriticalDepth.ReviewV2.nativeTheoremOne_proved` and `CriticalDepth.ReviewV2.standardTheoremTwo_proved`. The original native theorem-two interface also remains proved and audited.

## Trust and semantic scope

The workflow recompiles the project and consumer against freshly downloaded pinned dependency caches, with the locked Cli library built from source. Only a completed execution receipt establishes that those compilations succeeded. The Lean compiler, bundled runtime and pinned public dependency cache remain trusted. This is not a source rebuild of all Mathlib dependencies. Main and consumer compilation each use one Lean thread and a 6,144 MiB Lean memory limit; those flags are not an aggregate operating-system memory cap.

The [version index](../VERIFICATION_STATUS.md) identifies actual execution records. Local .verification files are diagnostic outputs and include local paths; publish only an explicitly selected portable evidence bundle. A guide or prepared script is not an execution receipt.

[Author semantic approval](../AUTHOR_SEMANTIC_APPROVAL.json) is separately bound to the approved manuscript, readable statements and Lean source. Named proposition guards are definitional checks, not an independent semantic specification. The [correspondence](LATEST_MANUSCRIPT_CORRESPONDENCE.md) and [proof-route ledger](../mathlib-review/CAD_VS_ALGEBRAIC_PROOF.md) explain the scope: the revised manuscript presents the existing algebraic route for the two main results. Its new End Matter cardinality estimates and counting discussion remain outside the formal interfaces.

## Advanced modes and history

The underlying main-only script also supports `CRITICAL_DEPTH_DEPENDENCY_MODE=trusted-cache` or `source-built` with explicit paths. For explicit roots, the directory basenames must be the nine package names (for example, mathlib and batteries), as enforced by verify_public_dependencies.pl. Source-built mode additionally needs its dependency-source receipt. These modes are separate from the clean release entry point.

Earlier execution records and timestamps remain under [verification-runs](../verification-runs/) and the [archive](../archive/README.md), with their original scope. The previously stopped dependency-source rebuild is not a requirement for the present cache-based release.
