# Manuscript-to-Lean correspondence

Publication manuscript: `manuscript/shallow_logical_operators_depth_threshold.tex`,
37,090 bytes, SHA-256
`18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85`.
It is a verbatim copy of the selected frozen input
`input_snapshot/current_manuscript_20261101_073646.tex`. An external source
change was detected by hash during the task; the user expressly chose the
current revision and retained all its modifications. These include the
author/email details, acknowledgement placeholder, figure layout, reference
and introductory changes, gate-count notation J, and the gcd notation d0.
The short left-panel arrow is already absent. No additional local mathematical
edits were made to this publication copy. All locations below refer to this
selected revision, not the earlier snapshot or its line-number offsets.

**Current-version verification passed.** The fresh run
`20261101T083613Z` compiled all 47 project modules and the root entry point.
The recursive audit covered 972 theorems, 1,296 mathematical constants, and
seven main targets. Source and artifact binding, module inventory, and all
46 mathematical module origins passed. The standalone public-root consumer
also passed. [VERIFICATION.md](VERIFICATION.md) records the receipts and scope.
**Author semantic review remains pending.** Internal AI review and kernel
acceptance are separate from author approval.

The regenerated **53-input** source manifest has SHA-256
`cdb7bde150cadbaa6e10ba24b1f38be560c582331d4385fb50b0486a1202b4a8`.
It binds the selected manuscript and current Lean/configuration/verifier
inputs. Author semantic approval must identify this manifest and publication
manuscript hash together.

| Source location | Formal meaning | Lean declaration or module |
| --- | --- | --- |
| Lines 268–287, Eq. correctable | Finite tensor register, isometric encoding, logical factor before gauge; every supported operator below distance compresses to gauge only | `CriticalDepth.Manuscript.Code`, `DetectsBelow`, `GaugeOnly` in `ManuscriptStatements` |
| Lines 289–295, Eq. encoded | One exact equation on all encoded logical and gauge states; both factors unitary | `CriticalDepth.Manuscript.Implements` |
| Lines 297–303 | Arbitrary finite lists of disjoint supported unitary gates, at most q sites each; one common total-depth budget | `arbitraryLogicalImage`, `arbitraryLogicalImageAtMost`; `CircuitNormalization`, `BudgetSemantics` |
| Theorem 1, label thm:depth, starting line 304 | h >= 1, q >= 2; finite projective logical image below the strict threshold, and non-density in PU(K) | `CriticalDepth.Manuscript.theoremOnePositive_proved` in `PositiveDepth` |
| Stronger core and exact-layer auxiliary targets | Common-budget results also permitting h = 0 and q = 1; exact layers have n padded gate slots | `theoremOneAtMost_proved` in `MainResults`; `theoremOne_proved`, `theoremOne_nondense` in `TheoremOne` |
| Numerical and two-sided support argument | ceil(log_q d), forward/backward cones, actual derivative insertion sum, distance detection after scalar extension | `Arithmetic`, `Support`, `ScalarExtension`, `FieldLightCone`, `FieldLayerDerivative`, `InsertionDetection` |
| Finiteness step of Theorem 1 | GL coordinate algebra with actual circuit points; derivation constants on prime fraction fields; finitely many minimal components and integral coordinate images | `CircuitParameters`, `CircuitSolutions`, `CircuitPoints`, `AlgebraicRigidity`, `FieldConstants`, `ScalarConstants`, `ComponentConstants`, `AlgebraicFiniteImage` |
| Critical-depth definition, Eq. critical-definition, line 439 | Minimum over positive budgets h >= 1, with infinity when there is no infinite image | `CriticalDepth.Manuscript.hInfinityPositiveAtMost` in `PositiveDepth` |
| Theorem 2, label cor:critical, starting line 450 | Qubit stabilizer subspace, actual distance d, k >= 1, q >= 2; first positive infinite budget exactly 2 ceil(log_q d) - 1 and a nontrivial continuous subgroup | `CriticalDepth.Manuscript.theoremTwoPositive_proved` in `PositiveDepth` |
| Positive versus nonnegative critical-depth bridge | Finite image at budget zero identifies the positive and nonnegative minima, including infinite values | `CriticalDepth.Manuscript.hInfinityPositiveAtMost_eq_hInfinityAtMost` |
| Stabilizer-distance witness | Arbitrary supported undetectable operator supplies a Pauli term of weight exactly d; stabilizer condition gives a nonscalar logical Hermitian involution | `PauliTensor`, `PauliSpan`, `StabilizerWitness` |
| Supported upper-bound circuit | Parallel Pauli compression, one rotation layer, reverse adjoint layers, on the original n qubits | `PauliConjugation`, `PauliCompression`, `PauliSynthesis`, `TheoremTwoReduction` |
| Continuous and infinite logical families | Exact continuous one-parameter subgroup; separate injective rational projective family | `Rotations`, `TheoremTwoReduction`, `BudgetSemantics` |
| Concrete hypotheses and core calls | Explicit [[4,2,2]] code, full stabilizer fixed-space, actual distance, and core budget-zero/critical-budget applications | `FourQubitExample`, `FourQubitStabilizer`, `MainExamples` |
| Current Theorem 2 concrete call | Closed application to the explicit [[4,2,2]] code: positive critical budget one and a continuous logical subgroup | `CriticalDepth.Manuscript.PositiveDepthExamples.fourQubit_positive_critical_subgroup` |
| Current Theorem 1 application schema | Five-site, distance-three code and detection property are supplied parameters; q = 2 and budget one | `CriticalDepth.Manuscript.PositiveDepthExamples.fiveSite_distanceThree_positiveBudget_schema`; this is not an explicit five-qubit code construction |
| Nonempty compression example | Five original qubits, X tensor Y tensor Z tensor I tensor I, weight 3, q=2, depth 3 | `PhysicalCompressionExample` |

The statements use finite complex matrix coordinates. Choosing orthonormal
bases identifies each finite-dimensional physical Hilbert space with a finite
complex coordinate space; the physical basis is the product of the local
bases. Adjoint, isometry, tensor order and supported action are explicit. The
package does not export a separate transport API taking arbitrary Lean
Hilbert-space carrier structures as input.

The author explicitly assumes K >= 2, g >= 1, n >= 1, d >= 2, arbitrary local
unitary matrices and disjoint supports within each layer. Theorem 1 uses a
distance lower bound only, with h >= 1 and q >= 2. Theorem 2 additionally assumes a qubit stabilizer
subspace with logical dimension 2^k, k >= 1, and actual distance d. Its
`HasActualDistance` contains both below-distance detection and a supported
undetectable witness of size d. Integer depth and arity parameters are natural
numbers with the stated inequalities.

The coordinate representation and complex scalars are the standard finite
quantum-system interpretation. Empty-support scalar gates are allowed and
absorbed into the gauge phase by a proved normalization. Only one overall
unit-modulus logical phase is quotiented out. No geometry, gate alphabet,
ancillas, intermediate-layer code preservation, or independent phase per
logical sector is added as an assumption.

The at-most budget is a finite union over exact lengths r <= h. It is not the
group generated by unrestricted products of shallow circuits. The upper-bound
family uses the original n qubits; the total circuit implements the logical
action. The critical-budget equality concerns infinitude of the whole logical
image, not the minimum depth of each individual rotation angle.

The current positive budget h still includes circuits of exact depth zero.
The restriction h >= 1 belongs to the budget parameter in Theorem 1 and to
the minimizing set in the current h-infinity definition. The core's separate
budget-zero and unary results remain available as extensions outside current
Theorem 1. `PositiveDepth` bridges the two critical-depth definitions using
the finite zero-budget image; this bridge passed the current build and audit.

The first theorem uses an alternate algebraic proof. The manuscript's CAD
stratification and End Matter are not formalized line by line. No whole-paper
correctness or novelty claim is made. See the two proof guides for dependencies.

Author review must assess this correspondence against the recorded manuscript
and Lean source hashes, including the coordinate representation, quantifiers,
gate-list normalization, common budget and projective quotient. No author
approval has been recorded for a frozen release of this package.
