> Historical review note (2026-11-02): status words and manuscript hashes below refer to that review. See [current approval](../AUTHOR_SEMANTIC_APPROVAL.json), [current correspondence](../docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md), and the [historical-status ledger](../docs/HISTORICAL_STATUS_NOTES.md).

# Manuscript → readable statements → Lean correspondence

This table maps the replay-reference manuscript M98e19 to statements S47a462 and the current Lean source. It is not a build receipt or author approval. The latest manuscript is assessed separately in ../docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md. Actual main and consumer results use the pinned trusted Mathlib cache and are recorded separately. **Author semantic approval: PENDING. CAD formalization: deferred.**

| Layer | File | SHA-256 |
| --- | --- | --- |
| M: replay-reference manuscript | `../verification-runs/20261102-3c90628/REFERENCE_MANUSCRIPT.tex` | `98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227` |
| S: readable statements | `ALIGNED_MATHEMATICAL_STATEMENTS.md` | `47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892` |
| F: complete Lean source | `CriticalDepthMathlib.lean` | `3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2` |

Locations below refer to these exact bytes. The
[historical correspondence at commit 5c602e32c66547a183f555e8c963e4621709fc90](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/5c602e32c66547a183f555e8c963e4621709fc90/mathlib-review/THREE_LAYER_CORRESPONDENCE.md)
is preserved separately. Its acceptance statements concern its historical
`85af...` formal source and do not establish acceptance of the present F.

In the tables, `R` abbreviates `CriticalDepth.ReviewV2`, `Manuscript` means
`CriticalDepth.Manuscript`, and `Arithmetic` means `CriticalDepth.Arithmetic`.
`F:L` links to line L of the complete source. Definition and bridge names
identify mathematical content; they do not substitute for actual audit output.

## Definitions and main results

| M: location and claim | S: normalized meaning | F: definitions, endpoints, and representation bridges |
| --- | --- | --- |
| Lines 258–267: finite complex factors and isometric encoding | §1, lines 7–17: `n ≥ 1`, logical dimension `K ≥ 2`, gauge dimension `g ≥ 1`, `V†V = I` | `Manuscript.PhysicalBasis` is the full product coordinate basis ([F:1496](CriticalDepthMathlib.lean#L1496)). Native endpoints take a raw Mathlib matrix and its isometry equation. `R.HilbertCoordinates` and `R.HilbertRegister` construct coordinates for actual finite complex inner-product spaces and tensor registers. |
| Supported physical operators | §1, line 19: arbitrary local operator tensored with complementary identity | `Manuscript.localEmbed`, `SupportedOn` ([F:1502](CriticalDepthMathlib.lean#L1502)); `R.HilbertLocality.embedOn`, `SupportedOn` ([F:10522](CriticalDepthMathlib.lean#L10522)); `R.HilbertMatrixTransport.supported_iff_coordinates` ([F:10663](CriticalDepthMathlib.lean#L10663)). The latter proves preservation of each physical support. |
| `eq:correctable`, lines 270–277 | §1, lines 21–35: all complex operators on every support of size `< d` compress to `I_L ⊗ M`; actual distance adds a size-`d` failure witness | `R.NativeGaugeOnly`, `NativeDetectsBelow`, `NativeActualDistance` ([F:9919](CriticalDepthMathlib.lean#L9919)); `R.HilbertMatrixTransport.gaugeOnly_iff_coordinates` and `detectsBelow_iff_coordinates`. Detection is not restricted to Pauli, Hermitian, or unitary operators. |
| `eq:encoded`, lines 279–285 | §2, lines 43–49: `UV = V(W ⊗ Z)` on all logical–gauge states, with unitary `W,Z` | The exact equation occurs in `R.nativeLogicalImage` ([F:9767](CriticalDepthMathlib.lean#L9767)). `R.HilbertCircuitTransport.implements_iff_coordinates` supplies its arbitrary-carrier bridge. `R.logical_factor_projective_unique` ([F:11645](CriticalDepthMathlib.lean#L11645)) proves uniqueness of the logical class under positive logical/gauge dimensions and isometry. |
| Lines 287–294: arbitrary gates and disjoint-support layers | §2, lines 39–41: arbitrary finite gate lists; arity at most `q`; no geometry or gate alphabet | `R.NativeGateData`, `NativeLayer`, `NativeCircuit`, and their allowed predicates ([F:9715](CriticalDepthMathlib.lean#L9715)). The carriers are finite lists/functions of actual Mathlib unitary elements. All support patterns and matrices remain quantified. |
| Empty-support phases and a common total budget | §2, lines 39–41, 57: some `r ≤ h` layers, including zero | `R.nativeLogicalImage` explicitly quantifies `∃ r, r ≤ h`. `Manuscript.arbitraryCircuit_normalization_phase` ([F:4337](CriticalDepthMathlib.lean#L4337)), `arbitraryLogicalImage_eq_logicalImage`, and `R.nativeLogicalImage_eq_preimage` justify reuse of the normalized model. Empty-support gates are not excluded from the input model. |
| Logical classes in `PU(K)` | §2, lines 49–59: one global unit-modulus scalar and the quotient group topology | `R.scalarPhaseSubgroup` ([F:9131](CriticalDepthMathlib.lean#L9131)), native `R.PU` and `projectiveMk` ([F:9162](CriticalDepthMathlib.lean#L9162)); `projectiveMk_eq_iff` and `R.HilbertPhase.logicalClass_eq_iff`. Nondensity concerns the unitary quotient itself. |
| `eq:depth`, lines 300–302 | §3, lines 63–75: strict bound `h < H(q,d)`, where `H = 2⌈log_q d⌉−1` | `Arithmetic.criticalDepth`, `clog_eq_natCeil_log`, and `criticalDepth_eq_log` ([F:106](CriticalDepthMathlib.lean#L106)). The ceiling and natural subtraction agree with the displayed formula under the stated `q,d ≥ 2` bounds. |
| `thm:depth`, lines 296–308 | §3: finite projective image and nondensity for every allowed circuit within one budget | `R.NativeTheoremOne`, `nativeTheoremOne_proved` ([F:10002](CriticalDepthMathlib.lean#L10002)); `R.HilbertCircuitTransport.theoremOne_arbitrary_carriers` ([F:11025](CriticalDepthMathlib.lean#L11025)). The latter derives the native hypotheses using support, detection, encoding, and full-image coordinate bridges. |
| `eq:critical-definition`, lines 425–439 | §4, lines 83–90: first positive budget with infinite image; empty-set value infinity | `R.nativeCriticalDepth` ([F:9984](CriticalDepthMathlib.lean#L9984)) is an `ℕ∞` infimum with explicit `1 ≤ h`. `nativeCriticalDepth_eq_legacy` connects the earlier positive-budget convention. Positive-budget images still contain depth-zero circuits. |
| Stabilizer subspace code in `cor:critical`, lines 442–451 | §4 and the added standard section, lines 140–158: whole common +1 eigenspace of an abelian Pauli subgroup excluding minus identity | `R.StandardPauliOperator` ([F:11741](CriticalDepthMathlib.lean#L11741)) independently lists phases `1,-1,i,-i` and concrete Pauli entries. `StandardPauliSubgroup` and `StandardStabilizerCode` ([F:11785](CriticalDepthMathlib.lean#L11785)) use an actual Mathlib subgroup and equality with the entire fixed space. |
| Relation to the original native stabilizer convention | Added standard section, lines 150–156: the extra group conditions are derived under isometry | `R.isPauli_iff_standardPauliOperator`; `pauli_subgroup_with_encoding_is_standard` ([F:11851](CriticalDepthMathlib.lean#L11851)); `scalar_member_of_stabilizer_eq_one`; `nativeStabilizer_iff_standard` ([F:11895](CriticalDepthMathlib.lean#L11895)). Anticommuting fixed Pauli members or minus identity would force `V = -V`, contradicting isometry on the nonzero domain. |
| Finiteness of the stabilizer subgroup | Added standard section, line 156: derived, not assumed | `R.pauliOperator_set_finite` ([F:11994](CriticalDepthMathlib.lean#L11994)), `standardPauliSubgroup_finite`, and `standardPauliSubgroup_finite_type` ([F:12014](CriticalDepthMathlib.lean#L12014)). The proof uses the finite phase/word image and injective unitary-to-matrix coercion. The order formula `2^(n-k)` is not a new formal target here. |
| Critical equality and nontrivial continuous subgroup | §4 and added standard section: same code/distance/arity hypotheses and critical total budget | The original `R.NativeTheoremTwo`, `nativeTheoremTwo_proved` remain ([F:10118](CriticalDepthMathlib.lean#L10118)). The selected standard-code endpoint is `R.standardTheoremTwo_proved : StandardTheoremTwo` ([F:11918](CriticalDepthMathlib.lean#L11918)); its only predicate replacement is justified by the two-way bridge. |
| Rotation construction, lines 455–480 | §5: one nonscalar Hermitian involution gives the exponential, exact projective kernel `πℤ`, circuit membership for every angle, and an exact closed circle range | `R.critical_circle_joint_witness` ([F:10167](CriticalDepthMathlib.lean#L10167)) binds these conclusions to the same generator. Physical synthesis is `Manuscript.pauli_rotation_synthesis` ([F:7614](CriticalDepthMathlib.lean#L7614)). No generator or synthesis witness is an extra main-theorem premise. |
| Concrete code applications | §6, line 137, and the added standard endpoint | Closed five-qubit calls `R.Examples.fiveQubit_native_depthOne` and `fiveQubit_native_depthTwo` ([F:11565](CriticalDepthMathlib.lean#L11565)); actual standard four-qubit call `R.StandardExamples.fourQubit_standard_critical_circle` ([F:11948](CriticalDepthMathlib.lean#L11948)). These use explicit code/isometry/detection or stabilizer/distance proofs, not a hypothetical five-site code. |

## Scope and differences

- Theorem 1 retains `n ≥ 1`, `K ≥ 2`, `g ≥ 1`, `d ≥ 2`, `q ≥ 2`, `h ≥ 1`,
  isometry, detection below `d`, and the strict depth bound. Backend extensions
  at `h = 0` or `q = 1` are not substituted for this statement.
- Theorem 2 retains physical qubits, gauge dimension one, logical dimension
  `2^k` with `k ≥ 1`, actual distance `d ≥ 2`, and `q ≥ 2`. Neither endpoint
  assumes Theorem 1, a logical Pauli, or its desired conclusion.
- The finite image consists of individually realizable classes within one
  total budget. It is not a bound on the group generated by arbitrarily long
  products. No ancilla, geometric locality, or intermediate code-preservation
  condition is added.
- The closed, nontrivial subgroup topologically group-isomorphic to `Circle`
  strengthens M's continuous one-parameter subgroup conclusion. Its image is
  contained directly in the critical-budget logical image. Special angles may
  admit shallower circuits; no per-angle depth lower bound is asserted.
- Selected native interfaces use Mathlib `Matrix.unitaryGroup`, `Subgroup`,
  `QuotientGroup`, quotient topology, `Circle`, and `ContinuousMulEquiv`.
  Arbitrary-carrier interfaces use Mathlib inner-product spaces, linear
  isometries, and actual tensor products. Their logical image is expressed in
  the native matrix `PU(Fin (finrank ℂ L))` through orthonormal coordinates.
  Legacy representations and their proved adapters remain in F; this is not a
  claim that every historical public declaration was removed.
- Support, detection, implementation, circuit budgets, and stabilizer status
  are article-specific predicates. The locality and full logical-image
  coordinate equivalences are proved bridges, not input assumptions.
  The nonempty physical basis needed by normalization follows from isometry
  and positive logical/gauge dimensions (`Manuscript.code_physicalBasis_nonempty`,
  [F:4294](CriticalDepthMathlib.lean#L4294)); it is not an extra main premise.

## Proof route and evidence boundary

The formal finiteness proof uses algebraic coordinates and derivations. It
does not certify the manuscript's CAD smooth-cell, root-branch, or path
arguments line by line; see [the CAD comparison](CAD_VS_ALGEBRAIC_PROOF.md).
That formalization is explicitly deferred. Physical Pauli compression proves
the supported-unitary conjugation and depth needed by the theorem; this table
does not claim a separate formal Clifford classification or a reproduction of
each basis-change/CNOT step in M's proof.

The source registry contains 41 targets, 29 exact-three targets, 13 named
proposition guards, and 12 Mathlib foundation checks. The merged source inventory contains 1,268 theorem declarations and 1,749 mathematical
constants. Separate component counts included one additional generated helper,
StandardTheoremTwo._proof_1; every hand-written declaration and original constant
is retained. The version-bound execution report records final acceptance. The only
permitted recursive axioms remain `propext`, `Classical.choice`, `Quot.sound`.

Source rebuild, kernel/audit execution, external consumption, publication,
timestamps, and version-bound author semantic approval are separate evidence.
This correspondence asserts none of those passes for the present F and is
not whole-paper validation.
