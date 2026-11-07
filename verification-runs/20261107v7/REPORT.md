# Independent replay and semantic review of 20261107v7

## A. Scope and version binding

The review covers the supplied v7 manuscript, its two main theorems, and Lemma 1 on finite evaluation images. Three separate Codex readers reviewed the two theorem interfaces and the verification boundary. The execution coordinator used a fresh checkout of main at **38bc10f39e085099f76b38cf200215aa0208fd61** with the additions listed in the input manifest. The supplied files were frozen and included in this release byte for byte. A different local draft with the same name was excluded by its hash.

| Object | SHA-256 |
| --- | --- |
| [Supplied TeX](../../manuscript/20261107v7.tex), 45,311 bytes | 70c261a982af5cbf4bb6a8784f5996a6d1ca9bf7ab34cc8b3ed5034a42adf271 |
| [Supplied PDF](../../manuscript/20261107v7.pdf), 469,716 bytes, 7 pages | ca3010f710a50fa394d40c651fdd5a5828e05b2871e9824e262236a0623f3137 |
| [Lean proof](../../mathlib-review/CriticalDepthMathlib.lean) | 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2 |
| [Readable aligned statements on the publication branch](../../mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md) | 330aec61416d6b191f47c7b6f717e1544ad51397e3aadda09920a46c6cfab95e |
| [Readable aligned statements used in the execution checkout](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/38bc10f39e085099f76b38cf200215aa0208fd61/mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md) | 47a462bdb4e0ca113940fa2263bd933e9c81737bc042aa93ad28d57b7be9b892 |
| [Earlier independent statement input](../../mathlib-review/inputs/original_pure_mathematical_statements.md) | 30a2707370aa7a79065d77e902b7630ddc303960d327d30448134b91fc83b305 |
| [Separate theorem caller](../../mathlib-review/SourceConsumer.lean) | 14556a208ecf58045e5124c836e2e1bf662a46292d8856674b728a26f7cc25d5 |
| [Dependency lock](../../lake-manifest.json) | b514bb81363b70f61906b8ed89400839126a4422186df8dfb46f2747e4371cc2 |

The article cites proof snapshot [ad6a378](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/ad6a378f6080ba32d92e7c31b6cf71b07685970a). The cited snapshot and the main baseline use the same Lean proof blob a532ac4e2af8a6e53d531c7fbbf68e16edc3cef0, caller, toolchain and lock. The re-executed verifier is the main version bound in the input manifest. The earlier proof snapshot and current main have separate branch histories.

The publication branch is revision/20261103v2-algebraic, based on 36198a6f7744da2c1198428f0f4df243d1841b96. The proof, caller, audit registry, toolchain and dependency locks on that branch match the execution bytes. The verifier differs only by its final local run-path message. The historical manuscript and statement introductions on the two branches have different bytes. [Executed inputs](EXECUTED_INPUTS.sha256) and [published inputs](INPUTS.sha256) are recorded separately. Earlier author approval and replay records are bound to their own manuscript versions.

Lean is pinned to 4.35.0, compiler commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Mathlib is pinned to 56a005855ea17e0b0958f73ec801ae140b0a1679, with the other eight public packages pinned by the same lock. The trusted public cache and Lean runtime were used as dependency artifacts. The project proof and caller were scheduled from source in new output directories.

All seven pages of the supplied PDF were rendered and visually checked. The theorem and lemma locations, the merged encoding identities in Eq. (4), and the combined propagated-insertion expression in Eq. (6) agree with the supplied TeX. The review binds the supplied PDF bytes separately from the TeX.

The user explicitly authorized the current cloud Codex service and its reviewers to read the supplied v7 pair and relevant project source and records. The semantic comparison itself was read-only. The user separately requested repository synchronization, a new execution, a saved report and RFC 3161 timestamps.

## B. Three-layer comparison

Lean locators refer to the proof source identified above. The aligned statement file is a correspondence document. The original pure mathematical statement input is historical and supplies a separate statement layer for both main theorems. A v7-specific author attestation is pending.

| Item | v7 manuscript | Readable statement | Lean declaration or definition | Judgment |
| --- | --- | --- | --- | --- |
| Finite systems and detection | TeX 73–90, finite tensor factors and isometry V, K ≥ 2 and g ≥ 1. Every operator supported on fewer than d subsystems compresses to identity on the logical factor. | Aligned §§1–2 and original Theorem 1. | CriticalDepth.ReviewV2.NativeDetectsBelow and NativeTheoremOne, near lines 9910–9934 and 10002–10015. Arbitrary Hilbert carriers are transported by HilbertCircuitTransport.theoremOne_arbitrary_carriers, lines 11023–11035. | 一致 |
| Exact gates and circuit budget | TeX 84–95 and Theorem 1, 208–222, PDF p. 1. Each circuit has total depth at most h, with disjoint supports of arity at most ρ in each layer. UV = V(W ⊗ Z) holds exactly. | Aligned §§2–3, q represents ρ. | nativeLogicalImage, 9767–9775, uses a witness r ≤ h, supported unitary gates and exact encoding. A supported full-register unitary is a local unitary tensored with identity on the complement. | 一致 |
| Strict depth and projective topology | Theorem 1, finite image and non-density for h < 2⌈logρ d⌉ − 1. The set concerns single circuits within the budget. | Aligned §3 and original Theorem 1. | CriticalDepth.ReviewV2.nativeTheoremOne_proved, 10002–10015. Natural-number ceiling log at 106–130 and homeomorphic transport to the actual PU quotient at 9198–9208. | 一致 |
| Finite evaluation image | Lemma 1, TeX 782–797, PDF p. 5. All derivations on each minimal-prime function field kill the coordinates, giving finite joint complex evaluation image. | No standalone Lemma 1 in the historical theorem handout. | CriticalDepth.evaluation_image_finite_of_minimalPrime_derivations, 3278–3286, for a Noetherian algebra. The circuit coordinates instantiate it at 7893–7913. | Manuscript → historical statement: 无法确认. Manuscript → Lean: 一致 |
| Circuit coordinate presentation | TeX 239–277. The manuscript recovers the encoded inverses from Q⁻¹ and diagonal blocks. | Aligned §3 specifies the mathematical image. | Lines 3359–3394 include logical and gauge inverse entries as separate variables. The same conjugation coordinates occur after substitution. | 存在差异 |
| Positive critical depth | TeX 460–468 and Theorem 2, 556–566, PDF p. 4. Ordinary qubit stabilizer codes with k ≥ 1 and actual d ≥ 2. The minimum is over positive depth bounds. | Aligned §§4–5 and original Theorem 2. | CriticalDepth.ReviewV2.standardTheoremTwo_proved, 11918–11932. nativeCriticalDepth, 9984–10000, and the native-to-standard bridge, 11895–11913. The ordinary stabilizer subspace has gauge dimension one. | 一致 |
| Exact one-parameter family | Theorem 2 proof, 569–603. The same nonscalar involution gives projective period π and rotations realized in the threshold budget. | Aligned §5, joint witness. | CriticalDepth.ReviewV2.critical_circle_joint_witness, 10167–10185, binds the same generator, exponential, exact πℤ kernel and image. The closed subgroup is continuously multiplicatively equivalent to Circle. | 一致 |
| Abstract's threshold scope | TeX 41–46 states the stabilizer threshold sentence for every code encoding at least one qubit without the distance guard of Theorem 2. | Both readable theorem statements require d ≥ 2. | StandardTheoremTwo has actual d ≥ 2 and q ≥ 2. | 存在差异 |

The two coordinate presentations admit mutually inverse maps. The common generators map identically in both directions. In the map from the larger presentation to the smaller one, substitute the polynomial inverse matrices recovered by the block formulas. The inverse relations in the larger algebra force exactly those entries by uniqueness of two-sided inverses. These maps preserve every conjugation coordinate and therefore the joint evaluation image. This is a source-level mathematical comparison. The pinned Lean proof checks its own presentation.

## C. Findings and unresolved scope

1. **Abstract distance guard.** Read as a standalone universal statement, the second abstract sentence at TeX 45–46 includes the trivial stabilizer [[1,1,1]] code. With ρ = 2, that code has infinitely many exact projective one-qubit gates at positive depth 1, while the stated expression evaluates to −1. Theorem 2 itself has d ≥ 2 and ρ ≥ 2. The publication preserves the supplied bytes.
2. **Compressed presentation.** TeX 225–230 pads to n slots. This is valid because disjoint nonempty supports give at most n gates per layer, and empty-support scalar phases can be absorbed into the encoding factors. In Eq. (6) at TeX 310, H_j denotes the displayed jth propagated term. These are exposition details in the attached revision.
3. **Boundary of the formal coverage.** The assertions about generated groups, fault-tolerant compilation and the single-gate-fault discussion are outside the two theorem interfaces. So are the End Matter Bézout bound and exact-counting procedure. The algebraic proof route covers the stated finite image. The older CAD proof is a separate historical route.
4. **Author semantics.** The exact v7 semantic review is model-assisted. The historical approval and pending records refer to other manuscript versions. The v7 author-review state is PENDING.

## D. Hypotheses and nonvacuity

Theorem 1 concerns a single finite code and a common budget, with no implication that arbitrary-length words generated by the shallow set form a finite group. Its finite image is proper in the infinite Hausdorff PU(K) for K ≥ 2. The standard integral reading of distance matches the Lean natural-number distance. If d is read as a real lower bound, integer support sizes and integer powers of ρ make replacement by ⌈d⌉ equivalent for both the detection cutoff and the strict threshold.

Theorem 2 uses actual distance, including a witness at that distance. The public standard theorem derives the weight-d Pauli and nonscalar Hermitian involution and uses the same exact implementation model for both bounds. The theorem concerns ordinary stabilizer subspace codes. A gauge-general subsystem extension falls outside this statement.

The main source and [caller](../../mathlib-review/SourceConsumer.lean) provide explicit five-qubit depth-one and depth-two cases with d = 3 for Theorem 1. The four-qubit [[4,2,2]] example with ρ = 2 calls Theorem 2 at threshold 1. The three named calls are fiveQubit_depthOne, fiveQubit_depthTwo and fourQubit_criticalDepth_and_closedCircle, under CriticalDepth.SourceConsumer.

## E. Replay and conclusion

**Lean checks passed; author semantic review pending (Lean 检查通过但语义待审).**

| Check | Fresh execution result |
| --- | --- |
| Integrated proof from source | PASS, Lean exit 0 |
| Recursive module audit | PASS, 1,268 theorem declarations and 1,749 mathematical constants. The 41-target registry has 29 exact-three checks, 13 named proposition checks and 12 foundation checks. No project axiom, imported project proof module or unapproved import was reported. |
| Independent caller against the new proof artifact | PASS, three closed theorem calls and two imported main theorem checks |
| Bundled kernel replay | PASS, leanchecker exit 0 for CriticalDepthMathlib and SourceConsumer |
| Direct recursive axiom queries | PASS, Lemma 1, both public main theorems, the arbitrary-carrier and joint-circle results, and the three callers use exactly propext, Classical.choice and Quot.sound |
| Public dependency source rebuild | Not run. The pinned public dependency artifacts were trusted and their before/after manifests matched. |
| Author review of the v7 correspondence | PENDING |

The [execution receipt](REPLAY.json), [input hashes](INPUTS.sha256), [elaborated target types](TARGET_TYPES.txt) and [recursive axiom output](TARGET_AXIOMS.txt) identify this run. The [extra query source](ReplayAudit.lean) and [Lemma 1 type query](LemmaType.lean) can be run with the fresh main and caller outputs on LEAN_PATH.

The first wrapper invocation completed the source audit and caller. Its optional checker launch failed because the isolated PATH did not contain the pinned lean executable. The published wrapper supplies that toolchain directory. The corrected checker commands ran successfully on the same artifacts, whose hashes were rechecked. The public-cache manifest covered 24,980 artifacts from nine pinned packages before and after the source audit.

The Linux task processes were serialized inside a cgroup v2 charged-memory boundary with memory.max = 7,899,996,160 bytes, zero swap, atomic process-tree entry and dropped privileges. The canaries tested descendant coverage, escape controls, aggregate pressure and file-mapping pressure. The production group's measured peak was 7,216,549,888 bytes. There were no OOM events. The 6 GB dispatch threshold was crossed during the source run, and the supplementary run was launched after the first group drained and current charge fell below the threshold. The receipt separates sample peaks, the lifetime peak and CPU time. These figures describe the isolated Linux processes and charged pages. The Windows launcher, other host processes and cloud inference are outside that metric.

The theorem bodies of the exact v7 manuscript correspond to the historical readable mathematical statements and the two public Lean interfaces, including the phase quotient and the total budget. In the reverse direction the checked Lean conclusions imply the stated theorem bodies under the ordinary stabilizer convention and the finite-system hypotheses. The unqualified abstract sentence has the narrower valid scope described above. The report and execution receipts bind the v7 files and the checked proof source separately.
