# Historical verification record and independent replay

**Historical record — VERSION_MISMATCH against the present manuscript.**

This page records the legacy release at
[c7e9b45](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/c7e9b4591c43c266947152b454f2008b12dc9f4c),
whose manuscript SHA-256 is
`18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85`.
The present manuscript SHA-256 is
`98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227`.
Recorded PASS results and source locations below apply to that historical input set.
They do not certify the manuscript now at the same repository path.

Use the [current Mathlib package](../mathlib-review/README.md),
[current correspondence](../mathlib-review/THREE_LAYER_CORRESPONDENCE.md), and
[version index](../VERIFICATION_STATUS.md) for the present release.
Within the historical account, words such as “current” mean current at the recorded legacy run.
This documentation correction does not rerun Lean, the axiom audit, or PDF inspection.
Author semantic approval remains pending.

## Replay routing

For the current 29-target integrated source, run from the repository root:

```sh
cd mathlib-review
lake exe cache get
sh verify.sh
```

The historical commands below concern the separate 47-module project and its seven targets.
Use a separate checkout pinned to the legacy release commit for a historical replay.
A fresh invocation of the root scripts on another commit checks that root project;
it does not replay the current 29-target Mathlib package.
The unchanged root script creates a new input inventory for each run and does not
validate the saved 53-row historical manifest.

## Historical run and instructions

**Lean checks passed; author semantic review pending.** This record binds the
then-selected historical manuscript (37,090 bytes, SHA-256
`18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85`).
The manuscript was copied verbatim with all selected revisions retained.

## Recorded historical checks

The fresh replay `20261101T083613Z` cleared prior project outputs, compiled all
**47 project modules** and the root `CriticalDepth.lean` entry point, and passed
examples, recursive axiom collection, source/artifact binding, final module
inventory, and audited-origin coverage. The audit covered **972 theorem
declarations** and **1,296 mathematical constants** in 46 mathematical modules,
including private, generated and unused helpers. Its own metaprogram driver is
excluded from the mathematical inventory.

All seven registered closing declarations compiled, were called from Lean
source, and passed the recursive axiom audit:

| Declaration in `CriticalDepth.Manuscript` | Scope |
| --- | --- |
| `theoremOnePositive_proved` | Historical manuscript Theorem 1, positive common budget |
| `theoremTwoPositive_proved` | Current manuscript Theorem 2, positive minimum |
| `theoremOne_proved` | Stronger exact-depth core |
| `theoremOne_nondense` | Core projective nondensity consequence |
| `theoremTwo_proved` | Exact-depth stabilizer core |
| `theoremOneAtMost_proved` | Common-budget core, including zero |
| `theoremTwoAtMost_proved` | Core minimum over nonnegative budgets |

Each target has exactly the recursive axiom set:

```text
propext, Classical.choice, Quot.sound
```

The audit rejects project-owned axioms and every recursive axiom outside that
allowlist. No `sorry`, `admit`, or `native_decide` proof is accepted. Six closing
types are checked against their exact named propositions; the seventh is the
explicit nondensity consequence. All seven elaborated types are printed with
implicit arguments, universes, full names, proofs and instances, followed by
head reduction under full transparency. This is not normalization beneath
every binder. See [audit.txt](../verification/audit.txt) and
[expanded-main-types.txt](../verification/expanded-main-types.txt).

The current Theorem 1 assumes q >= 2 and h >= 1. The stronger core also covers
h = 0 and unary gates at every finite budget; those are extensions outside the
current paper. The current Theorem 2 minimizes over positive budgets.
`PositiveDepth.lean` proves that budget zero is finite from the original code
and distance hypotheses, then equates the positive and nonnegative minima.
The main bridge adds no assumed zero-budget finiteness premise.

`PositiveDepthExamples.lean` calls current Theorem 2 on the explicit [[4,2,2]]
stabilizer code. Its current Theorem 1 call has concrete parameters
n=5, K=2, g=1, q=2, d=3, h=1, but takes a code and detection proof as parameters;
it does not construct a five-qubit code. Other checked examples include the
closed four-qubit core calls and a five-site physical Pauli compression circuit.
The separate [AuxiliaryCalls.lean](../verification/AuxiliaryCalls.lean) imports
the root package and calls exact finiteness and nondensity on the four-qubit
example. Its actual `lake env` run passed; see
[results.json](../verification/results.json).

The **53-input** [source manifest](../verification/source-manifest.sha256) has
SHA-256 `cdb7bde150cadbaa6e10ba24b1f38be560c582331d4385fb50b0486a1202b4a8`.
It covers all 47 module sources, the root source, three configuration/lock
files, the verifier script, and the selected TeX. The PDF has a separate
[byte and layout record](../verification/pdf-qa.json); the timestamp release
manifest additionally covers the PDF, documentation and verification records.
[results.json](../verification/results.json), commands, binding checks and
resource receipts report this current replay.

## Versions and dependency trust

| Component | Pin |
| --- | --- |
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Public package graph | Exact Git `rev` fields in [lake-manifest.json](../lake-manifest.json) |

The lock also pins Batteries, Qq, Aesop, ProofWidgets, importGraph,
LeanSearchClient, Plausible and Cli. A branch label in `inputRev` does not replace
its commit pin. Keep the toolchain, package configuration and lock unchanged.

Pinned public dependency artifacts are a **trusted bootstrap boundary**. This
run did not rebuild every external library from source. Missing external
modules were compiled from exact pinned Git blobs with Mathlib's corresponding
options. The task's own mathematical sources were freshly elaborated. No
private toolbox theorem is imported. Dependency downloads and cache retrieval
are preparation work, not proof verification.

## Execution boundary

All isolated Linux task tools and descendants ran inside one enforced
**8,000,000,000-byte aggregate cgroup limit**, with swap disabled. The user
explicitly approved excluding cloud models and the Windows desktop controller.
Lean invocations were serialized; `-j 1`, `-M 6144` and `LEAN_NUM_THREADS=1` are
additional process controls and do not establish the aggregate limit themselves.
The public verifier does not create an enclosing operating-system limit.

At replay completion the common cgroup's cumulative kernel peak was
5,972,230,144 bytes, including preceding isolated task work. The current replay's
sampled peak was 5,555,855,360 bytes. These are different metrics; no separate
per-job kernel peak is inferred. The memory event counters recorded no OOM.
The original [resource receipt](../verification/proof-run-resource.json) is kept.

Actual `lake check-build` and the separate root consumer under `lake env`
passed with the locked public package checkouts. These are configuration and
consumer checks. **A full `lake build` and a full Mathlib source rebuild were
not run.** Lake supplies the environment; it does not automatically pass Lean
flags to an arbitrary command or serialize all bootstrap hooks.

## Independent replay

Prepare Linux, the exact Lean toolchain, locked public package checkouts, and
matching trusted dependency artifacts. Record bootstrap/cache work separately.
Locked replay does not require `lake update`. Resolve any lock-file change
before claiming a replay of these inputs. To claim the same memory boundary,
enforce it around Lake and all descendants, including dependency preparation.

The concrete fresh-checkout bootstrap is in [README.md](../README.md). It uses the [documented Elan toolchain command](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/) and [pinned Mathlib cache command](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/README.md#L76-L83). The committed manifest is retained; no dependency-update command is needed.

Machine-specific compiled-output inventories and raw run records containing local absolute paths are omitted from publication. Portable commands and actual check outcomes remain in this guide, the verifier source and results.json. The verifier regenerates those inventories and checks their hashes during every replay; the actual accepted outcome is recorded in results.json.

From the repository root, inside that boundary:

```sh
sha256sum -c verification/source-manifest.sha256
lake check-build
lake env sh scripts/verify.sh
lake env lean -j 1 -M 6144 -DmaxHeartbeats=3000000 verification/AuxiliaryCalls.lean
```

The [verifier](../scripts/verify.sh) checks the pinned toolchain, puts the current
project output first on `LEAN_PATH`, rejects shadow project trees and unexpected
artifact symlinks, clears old outputs, and compiles every discovered module in
the checked dependency order. It includes the examples and the root entry point.
It then compares source hashes, artifact hashes, final source inventory, and
audited versus expected mathematical module origins.

A complete replay requires exit zero, the marker
`CRITICAL_DEPTH_AUDIT_PASSED theorem_count=972 constant_count=1296 main_count=7`,
and successful binding and module-set comparisons. Commands, times, exit codes
and logs are written under `.verification/<UTC timestamp>/`. A failed or
interrupted compiler invocation is not an accepted receipt.

## Correspondence and limits

Author semantic review remains pending; version selection alone does not
approve the Lean/manuscript correspondence. See [CORRESPONDENCE.md](CORRESPONDENCE.md).
The formal model uses finite complex coordinates and does not supply a separate
transport API from arbitrary Lean Hilbert-space carriers.

The first theorem uses the alternate GL coordinate-algebra proof in
[THEOREM_ONE_PROOF.md](THEOREM_ONE_PROOF.md), rather than the manuscript's CAD
stratification line by line. [THEOREM_TWO_PROOF.md](THEOREM_TWO_PROOF.md) describes
the stabilizer witness and original-qubit compression construction. The checks
do not establish every manuscript paragraph or its novelty, and do not concern
the group generated by unrestricted products beyond the common depth budget.
Timestamp evidence and its independent trust limits are recorded in
[timestamps/README.md](../timestamps/README.md).
