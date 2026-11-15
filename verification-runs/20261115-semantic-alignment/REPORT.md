# Semantic alignment and complete source replay — 2026-11-15

The revised manuscript now has a complete [mathematical statement file](../../docs/math/CURRENT_MATHEMATICAL_STATEMENTS.md) and a [three-layer correspondence](../../docs/CURRENT_THREE_LAYER_CORRESPONDENCE.md). The mathematical conclusions and all 346 Lean source files are unchanged. The fresh replay completed with **346/346 module compilations and 19/19 audit checks passing**. Exact results are in [REPLAY.json](REPLAY.json); the publication's document hashes are in [CURRENT_VERSION.json](../../CURRENT_VERSION.json).

## Changes and semantic review

The statement file covers the finite logical image, continuous onset, dense and exact generation thresholds, optimized fault exponents in all three metrics, the two saturation families, exact synthesis, Bacon–Shor and the concrete Q37 code. It makes the parameter ranges, quantifier order, recovery model and depth budgets explicit. The correspondence checks manuscript → statements and statements → Lean separately, and explains where a stronger formal endpoint implies the manuscript claim or uses a different intermediate argument.

The manuscript has four replaced source lines in three diff blocks:

- Line 89 now states the detectable-partition and global-phase conditions behind finiteness of transversal logical gates.
- Lines 761–762 point to the current version record and distinguish earlier timestamp bindings.
- Line 1258 defines noise locations as gates with nonempty support. Nonempty-support identity gates count; empty-support scalar gates do not.

No theorem, formula, proof or Lean declaration was revised. The statement file is a manuscript-led extraction checked against the formal interfaces in this revision. It is not an independently authored historical specification or a new author-approval record. Cross-review checked the principal hypotheses and conclusions, the CSS selection and rigidity interfaces, onset scaling, and the two clarified conventions. The linked tables record the scope of this semantic comparison; compilation alone does not establish it.

The verification guide now documents the full 346-module entry point. Earlier two-main-theorem scripts and their scope notes are labelled historical. Original approvals, release manifests and RFC 3161 timestamp files retain their bytes and scope; none is reassigned to the revised manuscript.

The repository's [.gitattributes](../../.gitattributes) disables line-ending normalization so a new checkout preserves the bytes bound by the manifests on Windows as well as POSIX systems.

## Version and execution binding

| Item | Observed value |
| --- | --- |
| Repository base | `dc1f6d7de3c9435be66c841095650f3bdb0ed72a` |
| Unchanged proof snapshot | `e22fb613f4463e0da04c1b0d6c2ea20eacf80c61` |
| `mathlib-review` tree at both commits | `ac7a3e6f4d945d5c89ff2355935d29c96bd9499b` |
| Lean | 4.35.0, compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Platform | Windows 11, AMD64; Python 3.12.14 |
| Start / finish (UTC) | 2026-11-15T03:24:59Z / 2026-11-15T04:30:46Z |
| Elapsed replay time | 3946.89 seconds |
| Project compilations | 346 passed, 0 failed |
| Required audit markers | 19 passed, 0 missing |
| Forbidden proof diagnostics | No matches |
| Input checks before / after | Passed |

[SOURCE_COMPARISON.json](SOURCE_COMPARISON.json) records the raw-byte comparison against both commits. All 346 Lean files and the six lock, toolchain and Lake configuration files match. No Toolbox package, private path or additional dependency is needed to compile this repository. The existing public dependency locks are unchanged.

The actual command was the following, using the recorded Python interpreter and an absolute path to a new output directory:

~~~sh
lake env python -B scripts/verify_full.py /absolute/path/to/new-output
~~~

The portable runner preserves the order, Lean flags and audit markers in `mathlib-review/verify-v3.sh`. It removes the old project build directory from the import path and checks that dependency roots do not shadow project modules. Every project module is compiled from source into the new output directory. The 9 locked dependencies, verifier, source inputs and dependency artifacts are hashed before the run and checked again at completion. The runner's negative-fixture self-test also passed.

## Evidence package

- [REPLAY.json](REPLAY.json): unchanged execution receipt, including all module exit codes, timings, marker results, and output hashes.
- [INPUTS.json](INPUTS.json): source, verifier and configuration hashes.
- [COMPILER_EVIDENCE.tar.gz](COMPILER_EVIDENCE.tar.gz): all 346 compiler logs, the full dependency source/artifact hash manifest, both input and execution records, and toolchain version output.
- [EVIDENCE_CONTENTS.json](EVIDENCE_CONTENTS.json): archive hash and hashes of every member.
- [TOOLCHAIN_PROVENANCE.json](TOOLCHAIN_PROVENANCE.json): official compiler archive provenance and the dependency bootstrap commands.

Extract the archive into a separate directory to inspect the receipt's relative evidence paths. The archive preserves each log and manifest byte-for-byte. Compiled `.olean` objects are not committed; their hashes remain in the receipt and the full command rebuilds them. The current version record binds the final manuscript, statements, correspondence, guide and these execution records separately. Its enclosing Git commit identifies the complete publication without a self-referential file hash.

Run `python -B scripts/check_current_version.py` to check the publication's hashes, source inputs, receipt and archive without compiling. This check passed on the final files and rejected a separate test copy with a changed statement document. It checks integrity of the recorded publication, not mathematical truth or authorship.

## Manuscript compilation

The revised [TeX](../../manuscript/Update_branch.tex) compiled successfully with the official Tectonic 0.17.0 Windows executable, producing the bound [21-page PDF](../../manuscript/Update_branch.pdf). [LATEX_CHECK.json](LATEX_CHECK.json) records the source and output hashes, engine, diagnostics and visual inspection. All 21 pages were rendered for a contact-sheet review; pages 1, 5, 9 and 10 were also inspected individually. The revised passages showed no visible clipping, overlap or black glyph boxes.

The final TeX log has no undefined or multiply defined references, missing characters, or overfull boxes. Its 12 underfull-box warnings and the 46 warnings from REVTeX's automatic BibTeX pass match a separate build of the pre-revision manuscript line-for-line. The manuscript supplies 45 bibliography entries directly; the final citations resolve. The retained environment/font-cache messages did not prevent rendering. The [original logs](latex/) preserve these details. The initial built-in compilation service timed out; the successful result above comes from the independent local Tectonic run.

## What the checks establish

Lean accepted the formal propositions under their definitions and hypotheses. The recursive audits reported only the permitted foundational axioms, `propext`, `Classical.choice` and `Quot.sound`, for the audited declarations and consumers; no project axiom, `sorryAx` or forbidden native-evaluation dependency was admitted by those checks.

This run trusts the installed Lean runtime and core library and the pinned public dependency artifacts. It is not a rebuild of the compiler or all dependencies from source, nor a separate `leanchecker` replay of all 346 modules. [The toolchain archive hash](TOOLCHAIN_PROVENANCE.json) matched the official release digest. This execution evidence does not by itself certify every handwritten intermediate argument, literature priority, or an independent human approval of the new statement file.
