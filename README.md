# Critical depth for the infinite logical set

This release provides one integrated Lean proof, a separate caller, the manuscript and a version-bound verification report. The Lean source imports public Mathlib modules and Lean's audit APIs; Mathlib is referenced as a pinned dependency and is not vendored.

**Mathematical verification: PASS. Author semantic approval: PENDING.** The two main interfaces recursively depend on exactly propext, Classical.choice and Quot.sound. See the [final report](verification-runs/20261102-3c90628/FINAL_VERIFICATION_REPORT.md) and [version index](VERIFICATION_STATUS.md) for the precise scope and resource qualification.

## Versions and dependencies

| Item | Version |
| --- | --- |
| Project | 0.3.0 |
| Lean | 4.35.0 |
| Lean compiler commit | eb6cafb7290e8bd5f2937522d8d804f58f02bafc |
| Mathlib commit | 56a005855ea17e0b0958f73ec801ae140b0a1679 |
| Transitive public packages | Exact commits in [lake-manifest.json](lake-manifest.json) |

The root [lean-toolchain](lean-toolchain) and [lakefile.toml](lakefile.toml) select this version. The sole default library is CriticalDepthMathlib, sourced from [mathlib-review/CriticalDepthMathlib.lean](mathlib-review/CriticalDepthMathlib.lean). The selected policy trusts the pinned Mathlib cache.

## Independent verification

In a clean checkout with the selected Lean toolchain:

~~~sh
lake exe cache get
sh scripts/verify.sh
~~~

The verifier compiles the project's source into a fresh output directory and checks the embedded recursive axiom audit against its source-bound registry. It checks 1,268 theorem declarations and 1,749 mathematical constants, including private/generated/unused declarations. Its 41 targets include 29 exact-three checks, 13 named proposition guards and 12 Mathlib-foundation checks.

[SourceConsumer.lean](mathlib-review/SourceConsumer.lean) separately calls the main results on explicit five-qubit and four-qubit codes. Its three closed proofs and two imported main theorems all pass exact-three checks. The [verification guide](docs/VERIFICATION.md) gives the complete build and fresh-artifact consumer commands. The actual run's [compact record](verification-runs/20261102-3c90628/VERIFICATION.json) links to the full [types and recursive axiom inventory](verification-runs/20261102-3c90628/KERNEL_AUDIT.txt).

## Main interfaces and mathematical meaning

- CriticalDepth.ReviewV2.nativeTheoremOne_proved proves finiteness and non-density of exact logical actions within one common total circuit-depth budget, under the stated detection and strict-threshold hypotheses.
- CriticalDepth.ReviewV2.standardTheoremTwo_proved proves the positive critical-depth equality and a nontrivial closed Circle-isomorphic subgroup for standard Pauli stabilizer subspace codes of actual distance d.
- CriticalDepth.ReviewV2.nativeTheoremTwo_proved retains the native interface. The proved nativeStabilizer_iff_standard bridge derives commutativity and exclusion of minus identity under the isometry hypothesis; finiteness of the Pauli subgroup is also proved.

The [aligned mathematical statements](mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md) and source definitions expose the assumptions. Named guards are definitional checks, not independent semantic specifications. Full target types are included in the audit; weak-head expansion does not normalize beneath every binder.

## Manuscript versions

The current manuscript is [20261104v1.tex](manuscript/20261104v1.tex), published on 2026-11-04 from the supplied file without byte changes. Its SHA-256 is `7777ecaefbaf8891090754c6cdb884e49f57c9d3bdd2a29c7451da120b9c860d`. The historical verification reports below are bound to the exact manuscript and Lean source versions recorded in those reports.

The 2026-11-02 release article is available as [TeX](manuscript/shallow_logical_operators_depth_threshold.tex) and [PDF](manuscript/shallow_logical_operators_depth_threshold.pdf), copied without edits.

The actual Lean replay used the earlier M98e19 reference manuscript. Its receipt is preserved unchanged. The [M1c17 manuscript correspondence](docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md) separately compares the M1c17 revision: paper rho corresponds to Lean q; Theorem 1 matches, and Theorem 2 matches under the ordinary [[n,k,d]] stabilizer-subspace reading (g=1). The new text omits the earlier explicit subspace/g=1 wording. A nontrivial-gauge extension and new universality/threshold discussion claims are not certified by this proof.

The [release binding](verification-runs/20261102-3c90628/RELEASE_BINDING.json) distinguishes latest article bytes, replay inputs and documentation-only changes. The exact [build inputs](verification-runs/20261102-3c90628/BUILD_INPUTS/) and [reference TeX](verification-runs/20261102-3c90628/REFERENCE_MANUSCRIPT.tex) remain available. No old receipt is relabeled as a new manuscript build.

## Scope and archived evidence

The user retained [author semantic approval](AUTHOR_SEMANTIC_APPROVAL.json) as PENDING; the [review packet](AUTHOR_REVIEW_PACKET.md) records the versions and interpretation. CAD formalization is deferred. The [proof-route comparison](mathlib-review/CAD_VS_ALGEBRAIC_PROOF.md) identifies the original smooth-cell/root-branch/path steps and the alternative algebraic formal proof.

The Lean compiler, bundled runtime and pinned public dependency cache remain trusted inputs. The final report separately discloses the configured 8 GB tool-group limit, a historical 4,096-byte accounting excess, and sampling limitations.

The [archive](archive/README.md) preserves the complete preceding main tree, including old sources, reports and timestamp collections, with its original bytes and relative paths. The current root has one proof entry. The user stopped the optional dependency-source rebuild and its temporary outputs were removed; it is not a remaining verification requirement.

[Timestamp evidence](timestamps/20261102-current/README.md) identifies the exact frozen collection and the separate RFC 3161 and OpenTimestamps outcomes.
