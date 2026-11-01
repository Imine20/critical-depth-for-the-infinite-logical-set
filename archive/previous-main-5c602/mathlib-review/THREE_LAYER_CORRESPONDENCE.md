# Manuscript → mathematical statement → Lean correspondence

**Final v2 integrated acceptance: PASS. Author semantic approval: PENDING.** The table maps actual definitions and proved component bridges. The completed whole-file audit is recorded in VERIFICATION.json; this table is not an author sign-off.

Layer M is the derived v2 manuscript `manuscript/shallow_logical_operators_depth_threshold.tex`, SHA-256 `98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227`. Its selected baseline is the observed desktop revision `118b256bde608d7f52fd11c783ba464a3eba65da2e46a2a333d4fffbbc380a1c`; it preserves that revision's editorial changes and adds the empty-support convention. The former published manuscript `18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85` remains frozen. The live desktop file is not assumed to retain an earlier hash.

Layer S is `ALIGNED_MATHEMATICAL_STATEMENTS.md`. Layer F comprises the named formal declarations below, assembled into the accepted v2-033 source `CriticalDepthMathlib.lean`. All names beginning `ReviewV2` below are relative to `CriticalDepth`; `Manuscript` and `Arithmetic` are also under `CriticalDepth`.

## Main correspondence

| Layer M: manuscript | Layer S: mathematical meaning | Layer F: actual definitions and bridges |
|---|---|---|
| Finite complex subsystems and an isometric encoding, immediately before `eq:correctable` | §1: arbitrary finite complex `Hᵢ`, `L`, `G`; `V†V = I`; `K ≥ 2`, `g ≥ 1` | Raw native targets quantify `Matrix … ℂ` and its explicit isometry equation. `ReviewV2.HilbertCoordinates` uses Mathlib finite inner-product spaces and linear isometries. `HilbertRegister` constructs the physical product register. |
| Operators supported on physical subsets | §1: an arbitrary local operator tensored with identity | `HilbertLocality.embedOn`, `SupportedOn`, and `embedOn_toMatrix_apply`; `HilbertMatrixTransport.local_embedding_coordinates` and `supported_iff_coordinates`. These prove locality preservation instead of assuming a global basis preserves support. |
| `eq:correctable`, line 272 | §1: every complex operator on every support of cardinality `< d` compresses to `I ⊗ M` | `ReviewV2.NativeGaugeOnly`, `NativeDetectsBelow`; `HilbertMatrixTransport.gaugeOnly_iff_coordinates` and `detectsBelow_iff_coordinates`. The quantifier is over all supported operators. |
| `eq:encoded`, line 280 | §2: `UV = V(W ⊗ Z)` on all logical and gauge states | The explicit matrix equation inside `ReviewV2.nativeLogicalImage` in `NativeCircuitModel`; `HilbertCircuitTransport.Implements` and `implements_iff_coordinates`. Logical/gauge unitaries are actual Mathlib unitary elements. |
| Logical factor determined up to phase after `eq:encoded` | §2: different gauge factorizations give one logical projective class | `ReviewV2.logical_factor_projective_unique` proves equality in the Mathlib-based quotient under the positive-dimension guards `K ≥ 1`, `g ≥ 1`, the isometry and the two factorization equations. It requires no detection hypothesis. |
| Gate and layer paragraph before `thm:depth` | §2: arbitrary finite gate lists, pairwise disjoint supports, arbitrary arity-`≤ q` unitaries, some `r ≤ h` layers | `ReviewV2.NativeGateData`, `NativeLayer`, `NativeCircuit`, `NativeGateAllowed`, `NativeLayerAllowed`; corresponding Hilbert circuit definitions and two-way `circuitToNative`/`circuitFromNative` conversions. All patterns and matrices remain quantified. |
| Explicit empty-support convention in that paragraph | §2: empty-support scalar gates may be absorbed into the gauge action without changing the image | The inherited `CircuitNormalization` and `BudgetSemantics` proofs normalize arbitrary lists. Native and Hilbert logical-image equalities preserve the resulting common budget. No empty-support restriction is silently added to the theorem. |
| Logical classes in `PU(K)` | §2: one global unit-modulus scalar; actual unitary quotient topology | `ReviewV2.scalarPhaseSubgroup`, `PU`, `projectiveMk`, `projectiveMk_eq_iff`, `puHomeomorphOld`; `HilbertPhase.logicalClass_eq_iff`. `PU` is a Mathlib quotient group, with proved compatibility with the earlier quotient. |
| `thm:depth`, line 296, and `eq:depth` | §3: positive `h`, `q ≥ 2`, strict bound `h < 2⌈log_q d⌉−1`; finite image and nondensity in actual `PU(K)` | `ReviewV2.NativeTheoremOne`, `nativeTheoremOne_proved`; arbitrary-carrier closing theorem `HilbertCircuitTransport.theoremOne_arbitrary_carriers`. `Arithmetic.criticalDepth` is the exact integer threshold. |
| All implementations under one depth budget | §2–3: each counted class has its own circuit within the same total bound | `nativeLogicalImage` quantifies `∃ r ≤ h` and all allowed circuits; `nativeLogicalImage_eq_preimage`, `nativeLogicalImage_finite_iff_legacy`; `HilbertCircuitTransport.logicalImage_eq_native` proves equality in both directions. |
| `eq:critical-definition`, line 431 | §4: minimum positive budget with infinite image, `∞` if none | `ReviewV2.nativeCriticalDepth` is an `ℕ∞` infimum with the explicit guard `1 ≤ h`. `nativeCriticalDepth_eq_legacy` proves equality with `Manuscript.hInfinityPositiveAtMost`. Depth-zero circuits remain included inside positive-budget images. |
| Stabilizer subspace code with actual distance in `cor:critical`, line 442 | §4: the entire encoding range is the common Pauli fixed space; detection plus a nongauge witness of support `d` | `ReviewV2.NativeStabilizer`, `NativeActualDistance`; proved `nativeStabilizer_iff_legacy` and `nativeActualDistance_iff_legacy`. Actual distance is not replaced by a lower bound alone. |
| Critical-depth equality and a nontrivial one-parameter subgroup | §4: `h∞ = H` and a closed nontrivial Circle-isomorphic subgroup contained in the critical-budget image | `ReviewV2.NativeTheoremTwo`, `nativeTheoremTwo_proved`; `stabilizer_critical_closed_circle`. The public theorem has no additional Theorem 1 or zero-budget-finiteness premise. |
| Pauli rotation argument around `eq:pauli-family`, line 476 | §5: actual exponential, exact kernel `πℤ`, and a closed circle, all for the same nonscalar Hermitian involution | `ReviewV2.critical_circle_joint_witness` packages all assertions jointly. Supporting names include `exp_involution_eq_rotation`, `projectiveRotation_eq_one_iff`, `circleRotationEquiv` and `mem_circleRotationSubgroup_iff`. |
| Positive-depth applications of `thm:depth` | §6: an actual distance-three five-qubit encoding at binary budgets one and two | `Manuscript.FiveQubit.encoding_isometry`, `detectsBelow_three`, `hasActualDistance_three`; `ReviewV2.Examples.fiveQubit_native_depthOne` and `fiveQubit_native_depthTwo`. These are closed calls, unlike the earlier parametric five-site schema. |

## Exact foundational objects

| Role | Mathlib object used in the v2 interfaces |
|---|---|
| Finite complex Hilbert carrier | `NormedAddCommGroup`, `InnerProductSpace ℂ`, `FiniteDimensional ℂ`; coordinates in `EuclideanSpace` |
| Encoding and changes of coordinates | `LinearIsometry`, `LinearIsometryEquiv`, `stdOrthonormalBasis`, `LinearMap.toMatrixOrthonormal` |
| Tensor product and local tensor maps | `TensorProduct` and `TensorProduct.map`; actual iterated binary tensors |
| Operators and adjoints | `LinearMap`, `LinearMap.adjoint`, `Matrix`, `Matrix.conjTranspose` |
| Unitary elements and groups | `unitary`, `Matrix.unitaryGroup` |
| Projective group and topology | `Subgroup`, `QuotientGroup`, quotient topology, `Dense`, `IsClosed` |
| Circle subgroup and equivalence | `Circle`, a `Subgroup` of `PU`, and a `ContinuousMulEquiv`, written `≃ₜ*` |
| Exponential | `NormedSpace.exp` on the matrix algebra |

Support, gauge-only compression, detection, actual distance, implementation, circuit budgets and stabilizer status are the manuscript's predicates. Defining them is explicitly permitted. The new raw-matrix targets do not require a custom `Code` input; the existing `Code` appears inside proved reuse adapters.

The internal register record organizes actual Mathlib spaces and orthonormal bases. Its empty tensor unit is one-dimensional, not an extra physical site or ancilla. The support split is built from local product bases and has a proved action on those basis vectors. The arbitrary-carrier result therefore does not depend on an unproved locality-preserving coordinate hypothesis.

## Quantifier and boundary checks

- Theorem 1 retains `n ≥ 1`, `K ≥ 2`, `g ≥ 1`, `d ≥ 2`, `q ≥ 2`, `h ≥ 1` and the strict depth inequality. Stronger backend extensions for `h = 0` or `q = 1` are not substituted for the current manuscript statement.
- Detection quantifies arbitrary supported complex operators. Gauge compression and implementation use the whole logical–gauge tensor space.
- Every allowed support pattern and unitary matrix is included. No gate alphabet, geometry, ancillas or intermediate encoding-preservation premise is introduced.
- Theorem 2 uses a genuine actual-distance witness. It retains the positive minimum and does not assume either the finiteness theorem or its conclusion.
- Nondensity is in actual `PU(K)`. It is not obtained by finding a zero or nonunitary matrix outside the logical image.
- The closed circle and exact projective period use the particular generator supplied under the original stabilizer hypotheses. They are not inferred from an arbitrary continuous real homomorphism.
- Critical-budget membership holds for every angle. There is no assertion that each individual angle has that minimal depth.

## Handout and acceptance binding

`HandoutBinding.original_theoremOne_proved` and `original_theoremTwo_proved` close the exact proposition bodies from the earlier pure Lean handout, whose SHA-256 is `964755075bb1a9f233e1c179b62732e080a2fbe08b7253163a9e7f0c679186b4`. The earlier readable mathematical handout has SHA-256 `30a2707370aa7a79065d77e902b7630ddc303960d327d30448134b91fc83b305`. The present Layer S is a separate aligned document; its exact bytes are recorded in `PAYLOAD_SHA256.txt` and the release manifest.

Component checks have passed through the arbitrary-carrier theorem and phase bridge (v2-030), the closed five-qubit calls (v2-028), and logical-factor uniqueness (v2-031). The completed v2-033 audit checked 1,251 theorem declarations and 1,727 mathematical constants, including private/generated declarations, 29 targets, 17 exact-three-axiom targets, 12 named guards and 12 imported Mathlib foundations. Own axioms and project/unapproved imports are zero. All mathematical constants satisfy the unchanged allowlist `propext`, `Classical.choice`, `Quot.sound`.

The assembled source has external Mathlib/Lean imports and inlines the project auxiliary proofs; it is not a short wrapper that requires importing the original project. Successful component imports alone do not establish acceptance of that assembled source. Pinned external artifacts, newly rebuilt missing dependencies, own source compilation, and fresh-clone reproduction remain separate evidence categories.

The formal finiteness proof uses algebraic coordinates and derivations. It is not a line-by-line formalization of the manuscript's CAD argument or `lem:finite-smooth-decomposition` at line 692. Final author semantic approval, current-byte publication evidence and timestamp coverage must be recorded separately; earlier receipts cannot attest new v2 files by implication.
