# Critical depth for the infinite logical set

This branch presents the algebraic-proof revision of 20261103v2. The article now uses the same coordinate-algebra and derivation mechanism as the existing Lean proof. Both main theorem statements and the Lean source are unchanged.

## Article

Download the [TeX](manuscript/shallow_logical_operators_depth_threshold.tex) or [PDF](manuscript/shallow_logical_operators_depth_threshold.pdf). The finite smooth-cell proof has been replaced, including the proof overview, Figure 1 and End Matter. The End Matter also derives a coarse explicit cardinality bound and discusses exact counting with algebraic input. These quantitative additions are not formalized in Lean. References remain ordered by first citation, with unused proof-specific references removed.

[RELEASE_BINDING.json](RELEASE_BINDING.json) identifies the article bytes, cited proof-and-scope snapshot, unchanged Lean source and historical replay evidence. The final publication is a descendant of its cited snapshot on revision/20261103v2-algebraic; later branch updates do not change the cited commit.

## Lean statements and verification

CriticalDepth.ReviewV2.nativeTheoremOne_proved establishes finiteness and non-density of the exact projective logical image under the strict threshold. CriticalDepth.ReviewV2.standardTheoremTwo_proved establishes critical-depth equality and a nontrivial closed Circle-isomorphic subgroup for ordinary qubit stabilizer codes of actual distance d.

Read the [scope statement](docs/LEAN_SCOPE_AND_CITATION_NOTE.md) and [mathematical statements](mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md). The algebraic finite-image proof includes the nonreduced case and does not assume that the physical parameter space is zero-dimensional.

The source is byte-identical to the source replayed at 411ff86bd30e423b3bc15267006e7bb3b409506d. The [existing clean-replay report](verification-runs/20261103v2-clean/FINAL_REPORT.md) records acceptance of the main source and independent caller, with no project axioms or sorryAx and main-theorem dependencies propext, Classical.choice and Quot.sound. This revision does not claim a new Lean run or extend the old receipt to new prose. Follow [the replay guide](docs/CLEAN_REPLAY.md) to reproduce that immutable source; [the version index](VERIFICATION_STATUS.md) distinguishes current and historical evidence.

The original author-approved input and approval record are preserved. The user subsequently requested this proof rewrite, the End Matter discussion and repository synchronization. The new quantitative material has not been added to the two formal theorem interfaces.
