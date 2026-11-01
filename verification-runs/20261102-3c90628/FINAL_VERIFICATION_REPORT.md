# Final verification report — 2 November 2026

**Mathematical validation: PASS. Author semantic approval: PENDING. Resource
result: qualified configuration/accounting result.** The current integrated
Lean source passed an actual compilation, recursive axiom audit and separate
external-consumer compilation using trusted pinned public dependencies.
This acceptance concerns the formal statements and exact versions below.
The subsequently supplied manuscript has a separate static correspondence
assessment; the original execution record is not retargeted to its new hash.

The evidence is [VERIFICATION.json](VERIFICATION.json), validated at
2026-11-01 17:01:55 UTC, and [KERNEL_AUDIT.txt](KERNEL_AUDIT.txt). Their SHA-256
hashes are respectively
`4d30510ea1f9379120a9187423d43b5bc7e94b1e296076b7ee531bec667da4fa`
and `aea2c0407ed7909ba8565f187e711777b2921760bf7ef76222b66d3087ab910a`.
The audit text contains all 41 complete target-type blocks and 1,749 recursive
constant records, rather than only a success marker.

| Actual replay input | SHA-256 |
| --- | --- |
| [Reference manuscript M](REFERENCE_MANUSCRIPT.tex) | `98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227` |
| [Aligned statements S](../../mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md) | `47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892` |
| [Integrated Lean F](../../mathlib-review/CriticalDepthMathlib.lean) | `3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2` |

F is 543,694 bytes. The later manuscript revision changed neither F nor S;
it adds text and claims outside this kernel replay. The immutable JSON retains
the reference M/S/F binding above.

The two current main interfaces and the retained native theorem-two interface
were individually checked for exactly `propext`, `Classical.choice` and
`Quot.sound`:

| Declaration in `CriticalDepth.ReviewV2` | Checked conclusion |
| --- | --- |
| `nativeTheoremOne_proved` | Finiteness and non-density of the exact logical image below the stated detection threshold, under one common total circuit budget. |
| `standardTheoremTwo_proved` | For the stated standard qubit stabilizer subspace-code hypotheses, critical depth `2⌈log_ρ d⌉−1` and a nontrivial closed subgroup topologically isomorphic to `Circle`. |
| `nativeTheoremTwo_proved` | The corresponding conclusion under the native whole-fixed-space stabilizer predicate. |

Their quantified isometry, dimension, distance/detection, positivity and budget
hypotheses remain part of the result. The standard-definition bridge derives
commutativity and scalar-phase exclusion from the native premises; Pauli
finiteness is derived from concrete finite phase/word data. A separate
stabilizer cardinality formula is not claimed.

| Embedded audit item | Actual result |
| --- | ---: |
| Own theorem declarations | 1,268 |
| Own mathematical constants, including private/generated/unused declarations | 1,749 |
| Registered full-type targets / exact-three targets | 41 / 29 |
| Named proposition guards / Mathlib foundation-origin checks | 13 / 12 |
| Own axioms / imported project modules / unapproved imports | 0 / 0 / 0 |

Every own mathematical constant has recursive axioms contained in the three
allowed names; the 29 designated targets require all three. No `sorryAx` or
additional axiom was admitted. The own-axiom scan includes the audit namespace.
Declared types and transparent weak-head types are printed explicitly, with
universes; this is not normalization beneath every binder. Named proposition
guards are definitional checks, not independently authored semantic specifications.

The foundation-origin records identify actual imported Mathlib declarations
for matrices, unitary groups, subgroups, projective quotients, `Circle`,
continuous multiplicative equivalences, Hilbert-coordinate objects and the
normed-space exponential. The selected native interfaces use these public
foundations. Compatibility declarations remain within the integrated source;
the zero-project-import result does not claim that every internal definition
was replaced by a Mathlib declaration.

The accepted jobs completed with compiler exit zero and signal zero. The
following are the actual Lean compilation intervals on 2 November, in
Asia/Shanghai (UTC+8):

| Job | Start | End |
| --- | --- | --- |
| 009, corrected main registry | 00:47:05.3882001 | 00:53:12.7593066 |
| 011, corrected external caller | 00:55:54.5196128 | 00:56:04.3814441 |

[SourceConsumer.lean](../../mathlib-review/SourceConsumer.lean), SHA-256
`14556a208ecf58045e5124c836e2e1bf662a46292d8856674b728a26f7cc25d5`,
elaborated three closed applications: the actual [[5,1,3]] code at depth
budgets one and two, and the actual [[4,2,2]] standard stabilizer code's
critical-depth/closed-circle conclusion. Its three proofs and two imported
main theorems all have exactly the standard three recursive axioms. The
caller imported the newly produced main artifact first, using the same
public dependencies. One frozen two-row main-artifact manifest was checked
before and after; source, dependency and artifact hashes were bound across
the checks. The accepted main `.olean` SHA-256 is
`57b4871e3934991aa11a48f091036beb5224891b6134b6d86a5cde142a117ecc`.

The toolchain is Lean 4.35.0, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; executable SHA-256 is
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`.
All nine public packages are fixed by the [dependency lock](../../lake-manifest.json),
SHA-256 `b514bb81363b70f61906b8ed89400839126a4422186df8dfb46f2747e4371cc2`.
The selected policy, `TRUSTED_PINNED_MATHLIB_CACHE`, follows the user's explicit
trust instruction. Mathlib is referenced through requirements, the lock and
imports, not vendored or recompiled for this replay. The compiler, bundled
runtime and pinned public artifacts remain trusted. The 3,699 actual public
imports were present in the sealed cache; this does not claim a dependency
source rebuild or an independently executed public fresh-clone replay.

The isolated tool group had `memory.max=8,000,000,000` and zero swap, with zero
OOM counters in both selected jobs. Resource status is
`ENFORCED_CONFIG_WITH_HISTORICAL_ACCOUNTING_OVERSHOOT`: its cumulative peak
was already 8,000,004,096 bytes before each job and remained unchanged.
At 0.2-second intervals, sampled group peaks were 7,536,156,672 bytes for the
main and 5,684,019,200 for the caller. Max-boundary events remained 5,835.
Linux permits temporary usage above `memory.max`; an unchanged cumulative
maximum does not exclude revisiting it, and periodic sampling can miss spikes.
Thus this report does not claim every instantaneous charge stayed within
8 GB or establish the excess's precise cause/duration.
[Official memory-interface documentation](https://docs.kernel.org/admin-guide/cgroup-v2.html#memory-interface-files).

Substantive unsuccessful attempts remain historical records. Job 007's Lean
process succeeded, but its outer verifier rejected predicted counts
1,269/1,750 against actual 1,268/1,749. Inspection found one shared generated
proof; all original 1,727 mathematical constants and 22 new constants remained,
with no missing handwritten declaration. Registry metadata was corrected
without changing F. Caller 010 failed implicit-argument elaboration; explicit
`n=4`, `k=2` annotations produced the accepted caller 011. Neither failure is
relabeled PASS. The earlier dependency-source attempt was user-stopped at
3,343/3,699 modules; approximately 2.77 GB of unfinished source/output trees
were removed, preserving records and the trusted cache. Its completion is
not a remaining verification gate.

The latest supplied [manuscript](../../manuscript/shallow_logical_operators_depth_threshold.tex)
is 35,519 bytes, SHA-256
`1c17ca04507174ce6b070af71a898626e279668d598d04b8b052787481d9ba0d`;
its 414,237-byte PDF has SHA-256
`582ca90c612a57e2e9fdfa67081ab661c7b547178ed66e7be02d75c7cca347e1`.
The [revision correspondence](../../docs/LATEST_MANUSCRIPT_CORRESPONDENCE.md)
records `STATIC_MATCH_TWO_MAIN_RESULTS_UNDER_STANDARD_SUBSPACE_READING`:
Theorem 1 matches after Lean `q` is read as paper `ρ`; Theorem 2 matches
ordinary [[n,k,d]] stabilizer subspace codes with `K=2^k`, `g=1`. The revision
removes explicit “subspace”/`g=1` wording, so no new `g>1` subsystem extension
is inferred. Its 37-qubit construction, generating-pair/universality,
compilation, fault-tolerance and threshold discussion is not formalized here.
CAD remains deferred; the existing algebraic finiteness proof does not verify
the manuscript's CAD steps. No whole-paper or PDF-layout/visual-QA claim is made.

The budget in the first theorem bounds each implemented operation's total
circuit budget. A group generated by arbitrarily long products is a separate
object. Neither the finite fixed-budget image nor the proved circle witness
establishes the revised discussion's dense generating pair or a fault-tolerant
threshold. Applying the generic theorem to a proposed external code would
still require supplying its actual code, isometry and detection/distance
hypotheses; the report supplies no such 37-qubit instance.

The user explicitly retained **PENDING** at 01:03 on 2 November. The
[author record](../../AUTHOR_SEMANTIC_APPROVAL.json) distinguishes the response's
reference version and the latest manuscript; no author approval is inferred or
requested again. Follow [the current verification guide](../../docs/VERIFICATION.md)
and [version index](../../VERIFICATION_STATUS.md). The complete preceding main
`5c602e32c66547a183f555e8c963e4621709fc90` is preserved byte-for-byte in the
[archive](../../archive/README.md), outside the sole current single-file build
entry. Timestamp status is recorded separately in
[the current timestamp collection](../../timestamps/20261102-current/README.md);
this report does not itself assert issuance or confirmation of those receipts.
