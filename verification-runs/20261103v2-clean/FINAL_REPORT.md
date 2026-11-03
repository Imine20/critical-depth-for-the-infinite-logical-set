# Independent replay of the 20261103v2 proof snapshot

**PASS.** This record concerns proof commit 411ff86bd30e423b3bc15267006e7bb3b409506d on branch release/20261103v2-verified. The final article cites that immutable snapshot. Its publication commit is a descendant and adds the final article, this evidence, and status documentation.

## Actual execution

The fourth bootstrap attempt ran in a new workspace on native ext4 under Ubuntu 24.04 / WSL2, backed by a task-owned filesystem image stored on E:. The filesystem was checked from both root and replay-user sessions. The bootstrap installed Elan 4.2.4 and Lean 4.35.0 anew, cloned the public repository at the exact proof commit, and downloaded the pinned public dependency cache into a new cache directory. It then compiled the locked Cli library from source with the Lake build cache disabled, because that library is absent from Mathlib's cache closure. No existing project compilation output or earlier task cache was used.

| Check | Result |
| --- | --- |
| Main source compilation | PASS, exit 0; 2026-11-02T20:36:58.034235358Z to 2026-11-02T20:42:38.995853674Z |
| Recursive inventory | 1,268 theorem declarations; 1,749 mathematical constants |
| Target registry | 41 targets; 29 exact-three targets; 13 named guards; 12 foundation-origin checks |
| Own axioms / project imports / unapproved imports | 0 / 0 / 0 |
| Independent caller | PASS, exit 0; 2026-11-02T20:43:03.674306058Z to 2026-11-02T20:43:07.925809658Z |
| Caller audit | 3 closed calls, 2 imported main theorems, 5 exact-three checks |
| Dependency checkouts | All 9 actual Git revisions match the committed lock; tracked source is clean |
| Integrity checks | Inputs, dependency artifacts and fresh main artifacts unchanged across their required checks |

Both main theorem interfaces recursively use exactly propext, Classical.choice and Quot.sound. The full types, declaration inventory and actual compiler outputs are retained in [evidence.tar.gz](evidence.tar.gz); its internal filenames match the unmodified [VERIFICATION.json](VERIFICATION.json). [EVIDENCE_MANIFEST.json](EVIDENCE_MANIFEST.json) hashes each archive member and the exported files. The archive contains no compiled project binaries.

[BOOTSTRAP.json](BOOTSTRAP.json) records all four attempts. At the earlier snapshot 7bc72f5, the first failed during TLS checkout (exit 128) and the second was rejected for missing Cli outputs (exit 2). At the corrected snapshot, the third was intentionally interrupted during dependency-artifact hashing on 9p/DrvFS (exit 143) to move the replay to native ext4. None of these three attempts reached project compilation. These unsuccessful attempts remain distinct from the fourth run, which used new task directories, a new toolchain and a new public cache. The proof source and verification checker were unchanged; the bootstrap correction builds the locked Cli library from source.

## Version binding and editorial checks

The replay-reference TeX has SHA-256 f3e86958f9a64f7d868e2f106fc1da833befe3223b733da46ad33958e5df2ad4 and is preserved as [REFERENCE_MANUSCRIPT.tex](REFERENCE_MANUSCRIPT.tex). The final article differs from it only in the immutable code-availability URL and its short commit identifier. The introduction, Lean-scope wording and clarified Bonet-Monroig attribution already belong to the replay reference. All other receipt-bound inputs, including Lean source, caller, statement file, approval record, dependency lock and verification scripts, retain their verified bytes.

The [release binding](../../RELEASE_BINDING.json) records final article hashes and this precise difference. The [editorial check](../../docs/20261103v2-editorial-check.json) also compares the final article with the author's approved input: it permits only the bibliography changes, availability/Lean-scope paragraph, requested introduction edit and clarified Bonet-Monroig attribution. Seventeen cited entries remain in first-citation order; Beverland is the sole removed, uncited entry. Surviving entries, theorem statements, equations and figures are byte-identical. Proof text is unchanged apart from the attribution sentence. TeX compilation exited zero, and all five PDF pages plus the embedded commit hyperlink were checked.

## Scope

The user explicitly approved the two main theorem semantics and accepted the independent algebraic proof route. [AUTHOR_SEMANTIC_APPROVAL.json](../../AUTHOR_SEMANTIC_APPROVAL.json) records that decision separately from execution. The CAD appendix is not formalized line by line. The result does not certify literature priority, every prose claim, or fault-tolerance constructions.

The Lean compiler, its bundled runtime and the pinned public dependency cache remain trusted inputs. This is a fresh project-and-caller replay on a host Linux environment, not a container/OS reconstruction or a full dependency-source rebuild. Main and caller each used one Lean thread and a 6,144 MiB Lean memory setting; no aggregate operating-system memory cap is claimed for this run.

Historical receipts and timestamps keep their original scope. Retained development notes with old PENDING/deferred wording are identified in the [historical-status ledger](../../docs/HISTORICAL_STATUS_NOTES.md).
