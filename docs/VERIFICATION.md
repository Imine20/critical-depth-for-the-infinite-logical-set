# Verify the complete current Lean project

The current full check compiles all 346 project modules and requires all 19 audit markers. The default Lake target covers only CriticalDepthMathlib; a default build does not check this entire scope. See the [current mathematical statements](math/CURRENT_MATHEMATICAL_STATEMENTS.md) and [three-layer correspondence](CURRENT_THREE_LAYER_CORRESPONDENCE.md).

## Pinned environment

Use Lean 4.35.0, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The remaining package revisions are fixed by [lake-manifest.json](../lake-manifest.json). Use Python 3.10 or later and Git. Do not update the dependency lock or reuse prebuilt project proof artifacts for a fresh replay.

The repository's [.gitattributes](../.gitattributes) disables line-ending normalization because the records bind exact file bytes. Use a fresh clone of this revision if an older checkout already converted those bytes. The verification commands preserve the checked-out sources.

Prepare the public dependencies from the repository root:

~~~sh
lake exe cache get
lake --no-cache build '@Cli/Cli:leanArts'
~~~

Mathlib's public cache does not supply the locked Cli library, so its source build is a separate step. The compiler, runtime and pinned public dependency cache remain trusted; this is not a source rebuild of the compiler and all of Mathlib.

## Full replay

~~~sh
lake env python scripts/verify_full.py /absolute/path/to/new-output
~~~

Replace the Python command with python3 or an absolute interpreter path as needed. The output directory must be absolute and must not exist. All project outputs are written there. The runner reads the module order and expected markers from [verify-v3.sh](../mathlib-review/verify-v3.sh), checks that the module list covers every project Lean file, and invokes Lean with the same compilation arguments. It uses the host's path-list separator, so it also supports native Windows:

~~~powershell
lake env python scripts/verify_full.py 'C:\path\to\new-output'
~~~

Each module is compiled with one Lean thread, a 6,144 MiB Lean memory limit and maxHeartbeats=3000000. These settings do not impose an aggregate operating-system memory cap. The runner binds source and verifier bytes, checks locked dependency revisions and tracked-source cleanliness, and checks that inputs and dependency artifacts do not change during the run. It records module results, audit markers, log hashes and generated artifact hashes in REPLAY.json. A failed or interrupted run is not a pass.

Success requires every module to finish with exit code zero, every expected marker to occur, no forbidden proof-placeholder/native-evaluation diagnostic, and all final binding checks to pass. Consult the actual receipt and compiler logs rather than inferring success from a started process or an existing output directory.

On a POSIX host, the original complete entry remains available:

~~~sh
lake env sh mathlib-review/verify-v3.sh /absolute/path/to/new-output
~~~

Use a new directory for this command as well. Its logs and checks cover the same module manifest; the portable runner additionally produces the structured binding receipt.

## Recursive axiom checks and semantic scope

The module audits enumerate project declarations and collect their transitive axiom dependencies. They reject project axioms and permit only:

~~~text
propext
Classical.choice
Quot.sound
~~~

The audits cover the baseline, generation results, physical code constructions, recovery and metric interfaces, both fault-suppression saturations, fixed-circuit exponents and consumers. A recursive axiom report establishes the dependency scope of the accepted formal propositions. It does not establish manuscript fidelity, the independence of an author approval, literature priority, or correctness of every handwritten intermediate argument.

The [current version record](../CURRENT_VERSION.json) binds the revised manuscript, statements, correspondence and actual replay receipt. [The version index](../VERIFICATION_STATUS.md) preserves the scope of earlier records. The current work does not relabel old approval or timestamp evidence.

To check that a downloaded publication still matches those document, source and evidence hashes, run:

~~~sh
python -B scripts/check_current_version.py
~~~

This read-only check verifies the existing publication, its evidence archive and the current timestamp payload's file bindings. It checks the timestamp receipt's recorded outcomes but does not reverify TSA signatures. Use the [current timestamp commands](../timestamps/20261115-current/README.md) for request, file, signature-chain and revocation checks. A fresh proof replay still requires the full command above.

## Historical baseline replay

The scripts verify_release.sh, replay.sh and clean_replay.sh under scripts/ implement the earlier two-main-theorem workflow. They compile CriticalDepthMathlib and SourceConsumer; they do not substitute for the current 346-module replay. The optional bundled leanchecker pass in that historical workflow also has that limited project scope. See [CLEAN_REPLAY.md](CLEAN_REPLAY.md) for its original bootstrap procedure and historical receipts.
