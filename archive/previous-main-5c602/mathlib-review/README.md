# Portable Mathlib verification package

The exact Lean source passed the recorded Lean 4.35.0 kernel build and recursive
axiom audit in run v2-033. Author semantic approval remains **PENDING**.

`CriticalDepthMathlib.lean` is the complete proof entry: 527,431 bytes, SHA-256
`85af30d2f9cdf217a729c004d7af0ad67f87b4a821eb28e38ae70dfec840dfd8`.
It imports 58 pinned Mathlib modules and two Lean modules, with all project
proofs included in this file. No project `.olean` is required.

The accepted audit covers 1,251 theorem declarations and 1,727 mathematical
constants, 29 registered targets, 17 exact-three-axiom targets, 12 named guards
and 12 Mathlib foundation origins. Own axioms, project imports and unapproved
imports are zero. The permitted recursive axioms are exactly `propext`,
`Classical.choice` and `Quot.sound`.

`KERNEL_AUDIT.txt` preserves all 1,727 recursive records and all 29 complete
target-type blocks from that actual run, together with the mathematical checks
and final marker. `VERIFICATION.json` contains selected mathematical results,
version pins and source bindings. Execution diagnostics are not part of this
portable release. The mathematical extraction does not constitute an
independent fresh-clone replay.

## Reproduce

Install the toolchain named in `lean-toolchain`, keep the dependency lock and
LF source bytes, then run from this directory:

```sh
lake exe cache get
sh verify.sh
```

The script checks every payload file, verifies the pinned compiler commit,
compiles the single proof source, rejects compiler failure, checks source
stability, and requires the exact final audit marker. Its generated results
stay in the relative `.verification` directory. It does not install an
aggregate memory boundary; the recorded run used an aggregate 8,000,000,000-byte
limit, no swap, and a sampled peak of 6,619,074,560 bytes. Lean `-M6144` alone
is a per-process setting. Pinned compiler and dependency artifacts remain a
trust boundary; a full rebuild of Mathlib is not claimed.

## Meaning and limits

`ALIGNED_MATHEMATICAL_STATEMENTS.md`, `THREE_LAYER_CORRESPONDENCE.md` and
`AUDIT_RESPONSE.md` explain the statements, quantifiers, definitions, closed
five-qubit examples and actual Mathlib interfaces. The two earlier handouts
are retained under `inputs` because their proposition bodies have explicit
closing proofs in the single source. The derived manuscript is under
`manuscript`; its TeX and PDF bytes are unchanged in this packaging revision.

The principal native targets are `CriticalDepth.ReviewV2.nativeTheoremOne_proved`
and `CriticalDepth.ReviewV2.nativeTheoremTwo_proved`. The arbitrary finite-Hilbert
carrier version of Theorem 1 is
`CriticalDepth.ReviewV2.HilbertCircuitTransport.theoremOne_arbitrary_carriers`.
The joint circle/exponential/period witness is
`CriticalDepth.ReviewV2.critical_circle_joint_witness`.

The accepted finiteness proof follows an algebraic route. It does not check
the manuscript CAD argument line by line or certify the entire paper.
Prose-to-formula correspondence still requires author review. This portable
revision changes packaging and documentation, with no new proof execution.
Timestamp evidence applies only to the exact files in its own release manifest.
