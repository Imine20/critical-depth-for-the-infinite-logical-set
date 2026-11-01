# Fresh Lean 4.35.0 verification report

**PASS for the requested build and recursive axiom checks. Author semantic approval remains PENDING.**

This report records a new execution against source revision **3361e6cbed703b1a8bebe2b1784e875311361076**, tree `e13005a2fa0349d9fe85a9954798ebcde87a4d2a`, of [critical-depth-for-the-infinite-logical-set](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/3361e6cbed703b1a8bebe2b1784e875311361076). It uses new compiler outputs and new execution receipts. The source snapshot was a byte-checked file export; no Git working-tree cleanliness claim is made.

Inputs: [manuscript](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/3361e6cbed703b1a8bebe2b1784e875311361076/manuscript/shallow_logical_operators_depth_threshold.tex), [mathematical statements](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/3361e6cbed703b1a8bebe2b1784e875311361076/mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md), [integrated Lean source](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/3361e6cbed703b1a8bebe2b1784e875311361076/mathlib-review/CriticalDepthMathlib.lean).

## Result for the two main theorems

| Lean declaration | Actual recursive axiom set |
| --- | --- |
| CriticalDepth.ReviewV2.nativeTheoremOne_proved | propext, Classical.choice, Quot.sound |
| CriticalDepth.ReviewV2.nativeTheoremTwo_proved | propext, Classical.choice, Quot.sound |

For each target, the set is **exactly** these three standard axioms. This assertion concerns axiom dependencies under the theorem's displayed mathematical hypotheses; it does not remove those hypotheses. Full declared types and fully transparent weak-head reductions appear in [KERNEL_AUDIT.txt](KERNEL_AUDIT.txt). Reduction does not normalize every expression beneath binders.

## Actual execution and source binding

- Lean: **4.35.0**, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, checked by the executable in this run.
- Lake: **5.0.0-src+eb6cafb**, reporting Lean 4.35.0.
- Locked Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`. All nine dependency source HEADs matched their lock revisions.
- Main source compilation: **2026-11-01T13:03:38.838282113Z to 2026-11-01T13:18:13.510679905Z UTC**, **874.672 seconds**, exit code **0** and normal phase exit.
- Command flags: `-j 1 -M 6144 -DmaxHeartbeats=3000000`; direct Lean compilation of the published single-file source with public cached dependencies.
- Main source: **527431 bytes**, SHA-256 `85af30d2f9cdf217a729c004d7af0ad67f87b4a821eb28e38ae70dfec840dfd8`.
- Manuscript SHA-256: `98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227`.
- Mathematical statements SHA-256: `b0a1108b54c4e5cd54499ce7fd32d7e05f9b4ad7a2220b4b22ad07b931c49c4f`.

The captured public tree was checked for 20 release records; 16 local package files were rechecked against their SHA-256 hashes and Git blob identities. Source bytes were checked before and after compilation. [VERIFICATION.json](VERIFICATION.json) binds the actual run to the source and newly generated output. [ARTIFACT_MANIFEST.json](ARTIFACT_MANIFEST.json) lists the compiler products and their hashes.

## Recursive audit coverage

| Check | Accepted count |
| --- | ---: |
| Theorem declarations in the integrated development | 1251 |
| Mathematical constants with recursive axiom records | 1727 |
| Registered targets with full type exports | 29 |
| Targets required to use exactly the standard three | 17 |
| Named definitional proposition checks | 12 |
| Actual Mathlib foundation-origin checks | 12 |
| Project-declared axioms | 0 |
| Imported project modules | 0 |
| Unapproved imports | 0 |

Every one of the 1727 mathematical constants has its recursive axiom set contained in `{propext, Classical.choice, Quot.sound}`. The inventory includes mathematical auxiliary, private and generated declarations; the audit driver's metaprogramming namespace is outside this mathematical inventory. The own-axiom scan includes all own namespaces. The source directly imports 58 Mathlib modules and two Lean modules. All target records, foundation origins and full type blocks were checked, rather than accepting the final count marker alone. `sorryAx` and every other extra axiom are rejected.

## Calls through the newly compiled module

[FreshConsumer.lean](FreshConsumer.lean) imports the new main artifact and makes three fully applied calls: theorem one on the actual five-qubit encoding at binary budgets one and two, and theorem two on the actual four-qubit stabilizer code of distance two. The last call proves positive critical depth one together with a nontrivial closed Circle-isomorphic subgroup at that budget.

The accepted caller run, **11/01/2026 21:20:46 to 11/01/2026 21:25:35 UTC**, exited normally with code **0**. Both imported main theorems originated in `CriticalDepthMathlib`. Recursive collection and printed axiom outputs agreed on exactly the standard three axioms for the two main theorems and all three caller theorems. The main artifact hash was checked before and after the caller. See [CONSUMER_VERIFICATION.json](CONSUMER_VERIFICATION.json).

The first optional caller attempt was rejected because a natural-number-to-extended-natural coercion was left unsimplified. The strict audit also rejected the resulting compiler recovery term. Adding `ENat.natCast_one` to the caller's simplification resolved that interface error; the integrated main proof source was unchanged. Failed attempt evidence remains preserved locally and is not treated as an accepted run.

## Resources and interpretation limits

The isolated Linux tools and descendants used an enforced aggregate **8000000000-byte** cgroup limit with swap disabled. Fresh synthetic controls tested inheritance, descendant tracking, blocked escape/broker routes, a successful under-cap allocation, an over-cap aggregate allocation, and file-mapping pressure. Production OOM counters remained zero, and the tool group was checked empty at completion. Raw system diagnostics and machine-specific paths remain private. Lean proof checking used the CPU; no GPU performance claim is made.

The pinned compiler and cached public dependency artifacts remain trusted inputs. This is a fresh build of the integrated project source, not a fresh rebuild of every Mathlib dependency or a separately performed public fresh-clone replay. Named proposition guards check definitional alignment and are not independent semantic specifications. The readable statements are not a second proof. The formal finiteness argument follows the published alternative algebraic route; the manuscript's CAD argument was not verified line by line. This run performs no new PDF visual review or author semantic approval.

Historical verification records and the existing stamped 20-file collection retain their original scope. This fresh report and caller are separate new records; no new cryptographic timestamp is claimed for them. The manuscript, integrated main source, dependency lock and existing portable package were unchanged.

## Independent replay

In a checkout containing the current proof package and this report directory, preserve the committed UTF-8/LF bytes and run:

~~~sh
cd mathlib-review
lake exe cache get
sh verify.sh
cp ../verification-runs/20261101-3361e6c/FreshConsumer.lean .
lake env sh -c 'LEAN_PATH="$PWD/.verification:$LEAN_PATH" lean -j 1 -M 6144 -DmaxHeartbeats=3000000 -o .verification/FreshConsumer.olean FreshConsumer.lean'
~~~

Use an appropriate enforced resource boundary when replaying. This recipe is provided for independent replay; the actual execution described above used the pinned executable directly with the recorded public dependency paths. The caller must report `FRESH_EXTERNAL_CONSUMER_PASSED call_count=3 imported_main_count=2 exact_three_count=5`, alongside normal exit and the source/artifact bindings.
