# Update_branch release record

- **Manuscript** [Update_branch.tex](../../manuscript/Update_branch.tex), 125,926 bytes, SHA-256 `bbdbefefd9f5b0fc8db465dbe679e885a64f7d6b063b5537dc29888572564e22`.
- **Supplied manuscript** 125,598 bytes, SHA-256 `ab55244ce633ae2ce1f0987f52059e00db70f6c98c01ff432fcdc7b915b02b0c`. The published source changes only Data availability and the `LeanRepo` bibliography entry. The wording, formulae and figures in the supplied mathematical text carry through to the release.
- **Lean proof snapshot** [e22fb613f4463e0da04c1b0d6c2ea20eacf80c61](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/e22fb613f4463e0da04c1b0d6c2ea20eacf80c61).
- **Timestamp evidence** [DigiCert RFC 3161 requests and responses](../../timestamps/update-branch/README.md) for the published TeX and [release input manifest](INPUTS.sha256.tsv).

## Manuscript-to-Lean correspondence

| Manuscript in this release | Lean declaration or module | Claim |
|---|---|---|
| Theorem 1, lines 313–325, and the finite-image lemma, 1054 ff. | [`theoremOne_arbitrary_carriers`](../../mathlib-review/CriticalDepthMathlib.lean#L11025), [`finiteEvaluationImage`](../../mathlib-review/Manuscript20261114Baseline.lean#L49) | The single-circuit projective image is finite and nondense below the distance threshold on arbitrary finite physical carriers. |
| Theorem 2(1), 510–515 | [`standardTheoremTwo_proved`](../../mathlib-review/CriticalDepthMathlib.lean#L11929) | The positive onset for an ordinary qubit stabilizer code of actual distance at least two is attained by a nontrivial closed circle subgroup. |
| Theorem 2(2), 516–520 | [`nativeExactDepth_eq_max`](../../mathlib-review/ExactGeneration.lean#L111) | The maximum formula includes infinite thresholds and uses the finite-dimensional encoding conditions. |
| Theorem 3, 707–745, and the correlated local-stochastic Pauli bound, 598–602 | [`sharpFaultSuppression_bounds_allMetrics`](../../mathlib-review/FaultPaperSaturationWitness.lean#L22), [`MidpointExactFaultWitness`](../../mathlib-review/MidpointExactFaultWitness.lean), [`paper_localStochastic_recovery_bounds_at_depth`](../../mathlib-review/FaultLocalStochasticPaper.lean#L21) | The original gate-list bounds apply to the three optimized errors. The upper-bound witness uses native midpoint faults, and the binomial lower-envelope guarantee also covers local-stochastic Pauli noise. |
| Fixed circuit, 1371–1382, and two-history ambiguity, 1393–1421 | [`historyErrors_firstUncorrectableOrder`](../../mathlib-review/FaultFirstBadOrder.lean#L125), [`paperCircuitErrorExponents_eq_firstUncorrectableOrder`](../../mathlib-review/FaultPaperFixedCircuit.lean#L19), [pointwise ambiguity](../../mathlib-review/FaultPointwiseAmbiguity.lean#L22) | The three separately optimized errors have the same first uncorrectable order, and an ambiguous pair incurs at least the smaller of its two probabilities. |
| Shor lower saturation, 1423–1554 | [`exists_shorGrouped_histories`](../../mathlib-review/ShorMultilayerSaturation.lean#L30), [`sharpFaultSuppression_lower_paper_witness_allMetrics`](../../mathlib-review/FaultPaperSaturationWitness.lean#L39) | A depth-exact original gate list on the distance-`d` Shor code attains the lower envelope, using genuine cross-cell gates and two equal-size fault histories for $h\ge 2$. |
| CSS rigidity and upper saturation, 1577–1934 | [physical rigidity](../../mathlib-review/CSSCircuitRigidity.lean#L40), [probabilistic existence](../../mathlib-review/CSSRandomRigidity.lean), [`sharpFaultSuppression_upper_paper_witness_allMetrics`](../../mathlib-review/FaultPaperSaturationWitness.lean#L75) | A single physical CSS code attains the upper envelope throughout $1\le h\le t$, with $t\ge20$ sufficient. The whole physical unitary is constrained under arbitrary native unitaries in the stated budget. |
| Exact synthesis and examples, 1966 ff. | [exact synthesis](../../mathlib-review/StabilizerNativeGivens.lean#L23), [Bacon–Shor](../../mathlib-review/BaconShorProposition.lean#L120), [Q37](../../mathlib-review/Q37ConcreteThreshold.lean#L43) | Finite constructive logical synthesis and the two threshold orderings have corresponding Lean results. |

## Verification scope

The [full-source replay record](../../mathlib-review/CONTINUATION_VERIFICATION.json) records 346 project modules and 19 recursive audit checks under `update_branch.clean_project_replay`. The [focused audit output](UpdateBranchAudit.log) gives the elaborated types and recursive dependencies of the principal declarations. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.

The earlier [comparison](../../FORMALIZATION_UPDATE_BRANCH.md) and execution record were prepared against manuscript SHA-256 `6f35f5aefb492372c0ce22050b5a06331c13e99b25bedab816088254c1a29ea9`. The independent read-only comparison inspected the supplied `ab55244c…` manuscript and the same accepted Lean source. The release edits affect only availability and citation. The execution record retains its original manuscript hash. Earlier author approvals apply to their recorded versions.

The bounded-depth image in Theorem 1 is the set realized by individual circuits within the budget. The manuscript's abstract statement about transversal finiteness uses the fixed detectable partition and projective-phase convention stated in the introduction. Some manuscript derivations, including estimates in the CSS existence argument, use different intermediate steps from the Lean proof. The correspondence above identifies the formal statements supported by the audited source.

## Reproduce

Use a fresh Linux or WSL checkout at the tagged publication or the proof snapshot. The compiler is Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`. All transitive package revisions are in [the lockfile](../../lake-manifest.json).

~~~sh
lake exe cache get
lake --no-cache build '@Cli/Cli:leanArts'
lake env sh mathlib-review/verify-v3.sh /absolute/path/to/new-output
~~~

The replay uses the pinned public dependency cache and builds the project modules from source. It checks every audit marker. See the [existing verification guide](../../docs/VERIFICATION.md) for resource isolation and the historical baseline checker.
