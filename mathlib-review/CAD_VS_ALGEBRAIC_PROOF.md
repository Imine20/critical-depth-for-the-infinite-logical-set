# Manuscript smooth-cell proof and independent algebraic formal proof

**Selected scope:** the two main theorem statements are formalized by an independent proof route. On 2026-11-03 the user explicitly approved the semantic correspondence and stated that the formalization need not reproduce the manuscript CAD route. CAD formalization is therefore outside this release's scope and is not a release blocker.

This comparison uses the selected manuscript input SHA-256 285ad9c537ad494418c250a6be1964476af1e6cd43b331a68733643a54d33ec2 and the integrated Lean source SHA-256 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2. Manuscript references below use the selected input's labels; source declarations refer to this exact Lean file. No claim about a future Git commit is needed to identify these bytes.

## Corresponding proof mechanisms

| Step | Manuscript route | Algebraic Lean route | Formal scope |
| --- | --- | --- | --- |
| Finite support arrangements | Theorem 1 pads to a common total budget and takes a finite union over support arrangements. | Finite gate-slot normalization, support arrangements and arbitraryLogicalImage_finite_of_logicalImage_finite (line 4439). | Arbitrary allowed supports, scalar empty-support gates and one total circuit budget are covered. |
| Gate insertions and frame transfer | eq:generator, eq:compression and eq:logicalgen use smooth gate derivatives, forward/backward light cones and gauge-only compression. | algebraic_forward_of_backward_frame (line 743), algebraic_gauge_frame_transfer (line 773), and derivation identities for circuit coordinates. | The product, inverse, locality and common-frame arguments are proved algebraically; no smooth family is assumed as an extra main-theorem premise. |
| Detection over an extension field | The manuscript applies detection to complex operators along a real smooth path. | detectsBelow_scalarExtension (line 4005) derives the extension-field law by linear span. | Extension-field detection is proved from the original complex detection hypothesis. |
| Polynomial constraints | Unitarity and the encoding identity define a real polynomial zero set in matrix coordinates. | The circuit coordinate algebra and generic circuit-point construction encode corresponding polynomial relations over the complex base field. | Physical admissible circuits yield evaluations; generic field-valued points are algebraic objects, not asserted to be physical unitaries. |
| Finiteness mechanism | lem:finite-smooth-decomposition constructs a finite sign-invariant smooth-cell partition. | isIntegral_of_minimalPrime_derivations (line 3251) and evaluation_image_finite_of_minimalPrime_derivations (line 3278) use Noetherian coordinate algebras and minimal-prime fraction fields. | A finite-evaluation-image criterion is proved, including nonreduced coordinate algebras. It is not a CAD partition theorem. |
| Constancy mechanism | eq:cellpath transports a segment through a smooth cell chart; eq:logicalgen gives scalar logical generator and projective constancy along the path. | isAlgebraic_of_forall_derivation_eq_zero (line 1435), exists_algebraMap_eq_of_forall_derivation_eq_zero (line 2612), and circuitPoint_projective_derivation_zero (line 7818). | Vanishing field derivations imply algebraic/base-field constants. No cell-chart or analytic path-integration proof is claimed. |
| Logical conclusion | One projective action per cell, then a finite union over arrangements. | circuitConjugationCoordinates_range_finite (line 7893), supportLogicalMatrices_projective_finite (line 7934) and logicalImage_finite_of_cone (line 7960). | The same main finiteness result is obtained using projective conjugation coordinates and finite evaluation images. |

## What the formalization does not certify

The manuscript's End Matter proof remains a separate written proof. The integrated Lean source does not formalize its sign-invariant smooth-cell induction, coefficient/truncation/minor projection argument, smooth square-free parts, ordered root branches, implicit-function construction, or transported smooth paths. A successful build of the independent route does not certify these manuscript steps line by line. This distinction is a scope statement, not a claim that those steps contain an error.

No rewrite of the article around the algebraic route is required by the current user instruction. A future project could formalize the CAD argument or present the algebraic proof in the article, but neither is a condition for this release.

## Sharp-threshold construction

Theorem 2 derives a weight-d nontrivial logical Pauli, compresses it with bounded-arity Clifford layers, applies one allowed rotation and reverses the compression. Its constructive proof does not use the manuscript CAD lemma. The standard stabilizer convention is covered by the proved native/standard equivalence and subgroup finiteness; this is completed mathematical source, not a still-proposed supplement.

The formal conclusion concerns exact code-preserving circuit actions. It does not certify protection against arbitrary faults in the central rotation gate.

## Evidence boundaries

[Semantic approval](../AUTHOR_SEMANTIC_APPROVAL.json), [current manuscript correspondence](../docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md), and [execution status](../VERIFICATION_STATUS.md) are separate records. This comparison establishes no fresh runtime result. Historical build receipts retain their original source and manuscript hashes; new clean-environment verification must be documented by its own receipt.
