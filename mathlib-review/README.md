# Integrated Lean proof and verification scope

"CriticalDepthMathlib.lean" is the complete integrated mathematical development. It imports public Mathlib modules and Lean audit APIs, with no imported project proof module. Its mathematical objects use Mathlib spaces, matrices, tensors, unitary groups, quotients, subgroups and topology. Article-specific predicates describe supports, circuits, detection and stabilizer conditions. Earlier representation declarations remain with proved bridges.

The proof source SHA-256 is 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2. Use Lean 4.35.0, compiler commit "eb6cafb7290e8bd5f2937522d8d804f58f02bafc", and the checked-in dependency lock. Mathlib is pinned to "56a005855ea17e0b0958f73ec801ae140b0a1679".

## Reproduction entry point

Run the current verification from the repository root using [the verification guide](../docs/VERIFICATION.md). The root registers this file as its sole current Lake library. The root verifier builds the project proof into a fresh output directory, checks the source-bound recursive audit and validates the selected dependency policy. The release workflow also checks a separate consumer against the newly built project output.

A clean checkout and a pinned public dependency cache provide a clean project rebuild. They do not imply that every public dependency was rebuilt from source. A dependency-source replay, when used, has separate commands and receipts. The Lean compiler, runtime and explicitly selected dependency artifacts remain part of the declared trust boundary. No successful execution follows from the presence of this README alone.

## Main interfaces

- "CriticalDepth.ReviewV2.nativeTheoremOne_proved" proves finiteness and non-density within a common total circuit-depth budget.
- "CriticalDepth.ReviewV2.HilbertCircuitTransport.theoremOne_arbitrary_carriers" provides the corresponding finite-dimensional Hilbert-space interface and preserves physical supports through the coordinate transport.
- "CriticalDepth.ReviewV2.standardTheoremTwo_proved" proves the sharp critical-depth equality and a nontrivial closed Circle-isomorphic subgroup for ordinary qubit Pauli stabilizer subspace codes of actual distance d.
- "nativeTheoremTwo_proved" remains available. The proved "nativeStabilizer_iff_standard" bridge identifies the native whole-fixed-space convention with the standard abelian-Pauli/no-minus-identity convention under the isometry hypothesis. Subgroup finiteness and the required scalar-member property are proved.

See [the stabilizer definition correspondence](STABILIZER_DEFINITION_CORRESPONDENCE.md), [the readable statements](ALIGNED_MATHEMATICAL_STATEMENTS.md), and [the current manuscript correspondence](../docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md). Historical manuscript locators in the readable statements are not current publication line numbers.

## Audit and immutable inputs

The embedded registry expects 1,268 theorem declarations, 1,749 mathematical constants, 41 registered targets, 29 exact-three targets, 13 named proposition guards and 12 Mathlib foundation origins. All own mathematical declarations must use no axioms outside "propext", "Classical.choice" and "Quot.sound"; registered exact-three targets must use all three. The scan includes private, generated and unused mathematical declarations and the audit namespace. Named guards are definitional checks, not independent semantic specifications.

"AUDIT_EXPECTED.txt" binds the expected complete marker to the exact proof source hash. "PAYLOAD_SHA256.txt" binds the listed source/configuration/document inputs; actual run reports and output hashes are stored separately to avoid circular input manifests. A standalone consumer is a distinct check and does not replace compiling the complete proof or auditing its dependencies.

Current execution evidence and its trust/resource qualifications are identified by [VERIFICATION_STATUS.md](../VERIFICATION_STATUS.md). Older "VERIFICATION.json" and "KERNEL_AUDIT.txt" files retain their historical scope and must not be relabeled as new runs.

## Approved semantics and proof route

The user approved the current two-main-theorem semantic review on 2026-11-03. [The approval record](../AUTHOR_SEMANTIC_APPROVAL.json) binds the selected manuscript input and unchanged mathematical source. No independently authenticated identity or exact approval time is asserted.

The manuscript's finiteness proof uses smooth cells and paths. The Lean proof uses an independent algebraic/derivation route, accepted by the user for this release. [The route comparison](CAD_VS_ALGEBRAIC_PROOF.md) describes the difference. Formalizing the CAD argument is outside this release's scope, not an approval or publication blocker. The mathematical conclusions, hypotheses and scope still have to match.

The formalization does not certify the entire article, its bibliography, a noise threshold, a universal generated gate set, a nontrivial-gauge extension of Theorem 2, or fault tolerance of the saturating rotation circuit.
