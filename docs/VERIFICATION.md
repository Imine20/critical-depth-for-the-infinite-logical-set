# Verify the current proof

The current root Lake target is **CriticalDepthMathlib**. Its complete proof source is [CriticalDepthMathlib.lean](../mathlib-review/CriticalDepthMathlib.lean). It imports public Mathlib modules and Lean's audit APIs; no private project proof modules are needed. Mathlib is referenced as a pinned dependency and is not vendored.

## Versions and dependencies

| Input | Required version |
| --- | --- |
| Lean | 4.35.0 |
| Lean compiler commit | eb6cafb7290e8bd5f2937522d8d804f58f02bafc |
| Mathlib commit | 56a005855ea17e0b0958f73ec801ae140b0a1679 |
| Other public packages | Exact revisions in the committed root lake-manifest.json |
| Main source and expected audit | SHA-256 and counters in mathlib-review/AUDIT_EXPECTED.txt |

Use the committed lean-toolchain and lake-manifest.json. Do not run lake update or substitute a moving Mathlib branch when reproducing this release. The nested portable package uses identical toolchain and dependency-lock bytes. The selected verification policy trusts the pinned Mathlib cache.

## Main build and recursive axiom audit

In a clean checkout of the release commit, with the selected Lean toolchain available:

~~~sh
lake exe cache get
sh scripts/verify.sh
~~~

The verifier allocates a fresh directory under .verification/current, compiles the current integrated source, runs its embedded audit and requires the exact source-bound audit marker. The run reports are generated outputs; the presence of this guide is not a successful-build receipt.

The embedded audit checks 1,268 theorem declarations and 1,749 own mathematical constants, including private/generated/unused declarations. Its registry has 41 targets, 29 exact-three targets, 13 named proposition guards and 12 Mathlib-foundation origin checks. All own mathematical declarations must have no recursive axioms outside:

~~~text
propext
Classical.choice
Quot.sound
~~~

The registered exact-three targets must use all three. The own-axiom scan includes the audit namespace. Target declared types and transparent weak-head types are printed without ellipses. This is not normalization beneath every binder; read the named definitions with the types.

The two main statement interfaces are:

- CriticalDepth.ReviewV2.nativeTheoremOne_proved
- CriticalDepth.ReviewV2.standardTheoremTwo_proved

The original native theorem-two interface, CriticalDepth.ReviewV2.nativeTheoremTwo_proved, remains proved and audited. The standard stabilizer bridge retains its full quantitative assumptions and conclusion.

## Compile a separate actual caller

[SourceConsumer.lean](../mathlib-review/SourceConsumer.lean) contains three closed calls using explicit five-qubit and four-qubit codes. Its audit checks those three proofs and the two imported main theorems for exactly the three listed axioms.

After a single successful main run in a clean checkout:

~~~sh
set -- .verification/current/run.*
test "$#" -eq 1
main_run=$1
test -s "$main_run/artifact.sha256"
(cd "$main_run" && sha256sum -c artifact.sha256)
public_paths=$(cat "$main_run/LEAN_PATH.local.txt")
lean_prefix=$(lake env lean --print-prefix)
caller_out=$(mktemp -d .verification/current/caller.XXXXXXXX)
LEAN_PATH="$main_run:$public_paths" LEAN_NUM_THREADS=1 \
  "$lean_prefix/bin/lean" -j 1 -M 6144 -DmaxHeartbeats=3000000 \
  -R mathlib-review \
  -o "$caller_out/SourceConsumer.olean" \
  -i "$caller_out/SourceConsumer.ilean" \
  mathlib-review/SourceConsumer.lean > "$caller_out/SourceConsumer.log" 2>&1
grep '^TRUSTED_CACHE_EXTERNAL_CONSUMER_PASSED ' "$caller_out/SourceConsumer.log"
~~~

The expected caller marker is call_count=3, imported_main_count=2, exact_three_count=5. If the checkout contains several previous runs, select the successful run by its source binding and complete audit result; do not identify an artifact only by modification time. The reference run additionally freezes the main artifact manifest and verifies the same artifact hashes before and after the consumer.

The verifier also supports an explicit trusted-cache path for an already installed pinned compiler and its nine public package output roots. Set CRITICAL_DEPTH_DEPENDENCY_MODE=trusted-cache, CRITICAL_DEPTH_LEAN to the absolute executable, and CRITICAL_DEPTH_PUBLIC_LEAN_PATH to the nine absolute cache output roots. Do not supply a source-build receipt in this mode. This route invokes the selected Lean directly; it does not rebuild Mathlib.

## Evidence and scope

See [the version index](../VERIFICATION_STATUS.md) for the actual current main build, recursive axiom audit, consumer result, source hashes and linked execution report. The complete mathematical audit supplies the target types and constant-by-constant recursive dependencies. A named proposition guard is a definitional check, not an independently written semantic specification.

The selected dependency policy trusts the Lean compiler, bundled runtime and pinned public Mathlib cache. The user's optional dependency-source rebuild was stopped incomplete and is not a current acceptance requirement. A per-process memory flag does not enforce an aggregate limit; the reference run separately records its isolated 8,000,000,000-byte tool-group limit and zero swap.

The [three-layer correspondence](../mathlib-review/THREE_LAYER_CORRESPONDENCE.md) and [standard stabilizer supplement](../mathlib-review/STABILIZER_DEFINITION_CORRESPONDENCE.md) describe the manuscript-to-definition mapping. Author semantic approval is separately version-bound. CAD formalization is deferred; the [proof-route ledger](../mathlib-review/CAD_VS_ALGEBRAIC_PROOF.md) gives the exact boundary.

Historical source, reports and timestamp collections are preserved in the [archive](../archive/README.md). They are not alternative current acceptance records. Signed timestamps establish existence of their named bytes, rather than correctness or authorship.
