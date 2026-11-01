# Portable current Lean source

`CriticalDepthMathlib.lean` is the complete integrated mathematical development. It imports 58 Mathlib modules and two Lean modules; it imports no other project module. Its public mathematical objects use Mathlib spaces, matrices, tensors, unitary groups, quotients, subgroups and topology. Article-specific predicates describe support, circuits, detection and stabilizer conditions. Legacy representation declarations are retained with proved native bridges.

Use Lean 4.35.0, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and the checked-in lock. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The ordinary cache-based check in this directory is:

~~~sh
lake exe cache get
sh verify.sh
~~~

The repository root registers this same source as its sole current Lake library. Its `scripts/verify.sh` also supports a source-built dependency mode, with an explicit pinned Lean executable, nine newly compiled public output roots, and a source-build receipt. See the root source-rebuild instructions and portable helpers. This is a rebuild of the proof's imported public modules, not of unrelated Mathlib modules. Bundled Lean/Std/Init/Lake and retained nonproof UI data are declared separately as inputs.

The two current theorem interfaces are `CriticalDepth.ReviewV2.nativeTheoremOne_proved` and `CriticalDepth.ReviewV2.standardTheoremTwo_proved`. The original `nativeTheoremTwo_proved` interface is retained. `nativeStabilizer_iff_standard` proves the standard abelian-Pauli/no-minus-identity convention equivalent to the native entire-fixed-space convention under the already required isometry. The standard subgroup's finiteness and scalar-member identity are proved, not added as hypotheses. See [the definition correspondence](STABILIZER_DEFINITION_CORRESPONDENCE.md) and [the readable statements](ALIGNED_MATHEMATICAL_STATEMENTS.md).

The embedded audit covers 1268 theorem declarations,1749 mathematical constants,41 registered targets,29 exact-three targets,13 named proposition guards and 12 Mathlib foundation origins. All own mathematical declarations must use no axioms outside `propext`, `Classical.choice`, `Quot.sound`; the registered exact-three targets must use all three. The own-axiom scan includes the audit namespace. Declared and fully transparent weak-head target types are exported without ellipses; predicates beneath binders still need their definitions. Named guards are definitional checks, not independent semantic specifications.

`AUDIT_EXPECTED.txt` binds the expected complete audit marker to the exact source hash. `PAYLOAD_SHA256.txt` covers immutable source/configuration/document inputs. Generated run reports and their output hashes are kept separately to avoid a circular input manifest. Consult `VERIFICATION.json`, `KERNEL_AUDIT.txt` and the repository's version index for the actual executed run and approval state; the presence of this README is not a build receipt or an author approval.

The manuscript CAD proof is preserved and its formalization is deferred by the user. The formal finiteness proof uses an alternative algebraic route. [The exact CAD comparison](CAD_VS_ALGEBRAIC_PROOF.md) lists the unformalized smooth-cell, root-branch and path steps. These readable files are not a second independent mathematical proof. The historical 47-module root project and older timestamp collections retain their immutable historical scope.
