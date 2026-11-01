# Critical depth for infinitely many logical operations

Manuscript and Lean **4.35.0** formalization of the two main depth-threshold
claims in `shallow_logical_operators_depth_threshold.tex`.

**Current-version proof verification passed.** The fresh run
`20261101T083613Z` compiled all 47 project modules and the root entry point,
including the current positive-depth targets and their examples. The recursive
audit covered 1,296 mathematical constants, including 972 theorems, and all
seven named main targets. Source and artifact binding, module inventory, and
coverage of all 46 mathematical module origins passed. The main targets use
only `propext`, `Classical.choice`, and `Quot.sound`.

**Author semantic review remains pending.** The selected manuscript is
37,090 bytes, SHA-256
`18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85`.
Compilation and axiom checks do not constitute the author's approval of its
correspondence with the Lean statements.

Layers contain arbitrary unitary gates on pairwise disjoint supports of at
most `q` original sites. The mathematical targets are:

1. For a finite subsystem code on `n >= 1` sites, assume logical dimension
   `K >= 2`, gauge dimension `g >= 1`, and detection of every operator on
   fewer than `d` sites, where `d >= 2`. All exact logical operations
   obtainable with a common total-depth
   budget `h >= 1` with `h < 2 ceil(log_q d) - 1`, for `q >= 2`, form a finite
   set modulo one global phase. The resulting set is not dense in the
   projective unitary group.
2. For a qubit stabilizer subspace code of actual distance `d >= 2` encoding at
   least one qubit, the first **positive** budget admitting infinitely many
   projective logical operations is exactly `2 ceil(log_q d) - 1`, for
   `q >= 2`. At that depth there is a nontrivial continuous logical subgroup.
   Gates are arbitrary unitaries on at most `q` of the original physical qubits.

The current-manuscript declarations are
`CriticalDepth.Manuscript.theoremOnePositive_proved` and
`CriticalDepth.Manuscript.theoremTwoPositive_proved`, in
[`CriticalDepth/PositiveDepth.lean`](CriticalDepth/PositiveDepth.lean).
Both passed the current build and recursive audit. Stronger core targets
remain in [`CriticalDepth/MainResults.lean`](CriticalDepth/MainResults.lean).
They also cover budget zero and unary gates, which are extensions outside
the current paper's Theorem 1. Receipts and verification limits are recorded in
[`docs/VERIFICATION.md`](docs/VERIFICATION.md).

`PositiveDepthExamples.lean` calls current Theorem 2 on the explicit
`[[4,2,2]]` code. Its five-site, distance-three Theorem 1 application is a
generic schema with a supplied code and detection proof; it does not
construct a five-qubit code. Both applications passed. The separate
`PhysicalCompressionExample.lean` exercises compression and depth-three
synthesis of a weight-three Pauli on the full five-qubit register.

The proof of the first result uses an algebraic coordinate-ring argument.
It does not formalize the manuscript's CAD stratification argument line by
line. The model uses finite complex matrix coordinates and does not export a
separate transport API from arbitrary Lean Hilbert-space carriers. The proof
routes and circuit-model correspondence are documented in
[`docs/THEOREM_ONE_PROOF.md`](docs/THEOREM_ONE_PROOF.md) and
[`docs/THEOREM_TWO_PROOF.md`](docs/THEOREM_TWO_PROOF.md).

Prepare the pinned toolchain, locked public dependencies, and matching caches
separately. Cache retrieval is bootstrap work, not proof verification; locked
replay does not require `lake update`. Keep the exact Git revisions in
[`lake-manifest.json`](lake-manifest.json), Lean 4.35.0, and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The current 53-input
[`source manifest`](verification/source-manifest.sha256) has SHA-256
`cdb7bde150cadbaa6e10ba24b1f38be560c582331d4385fb50b0486a1202b4a8`.
A fresh Linux checkout can bootstrap with Git, Elan and curl available:

```sh
git clone https://github.com/Imine20/critical-depth-for-the-infinite-logical-set.git
cd critical-depth-for-the-infinite-logical-set
sha256sum -c verification/source-manifest.sha256
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
```

Then run the manifest check and project verifier below. Cache bootstrap may
build its own executable; it is separate from the recorded project proof check.
This is a reproduction recipe, not a claim of an additional fresh-clone run.

From the prepared repository root, run:

```sh
sha256sum -c verification/source-manifest.sha256
lake check-build
lake env sh scripts/verify.sh
```

The script compiles project modules sequentially, compiles concrete main-result
calls, checks the public entry point and runs `CriticalDepth/Audit.lean`.
It records commands, source hashes, logs and exit codes under `.verification/`.
Dependency initialization and cache retrieval are separate from project proof
checking. The session's aggregate memory boundary and trusted dependency-cache
scope are recorded separately; a Lean `-M` flag alone is not an aggregate cap.

An optional standalone consumer imports the public root and calls its targets:

```sh
lake env lean -j 1 -M 6144 -DmaxHeartbeats=3000000 verification/AuxiliaryCalls.lean
```

This consumer passed for the current package; see
[`verification/results.json`](verification/results.json).
`lake check-build` is a configuration check; no full `lake build` result is
claimed. The sequential verifier above supplies the recorded project proof
replay.

The publication manuscript is the user's selected current input, copied
verbatim with all its modifications retained, including author/email details
and the acknowledgement placeholder. Its left-panel arrow was already absent;
no additional local mathematical edits were made to this copy. Byte bindings,
current source locations, and pending semantic review are recorded in
[`docs/CORRESPONDENCE.md`](docs/CORRESPONDENCE.md).

Separate timestamp receipt status is tracked in
[`timestamps/README.md`](timestamps/README.md).
