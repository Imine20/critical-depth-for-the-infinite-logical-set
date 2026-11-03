# Lean scope and Bonet-Monroig citation

## Formal result scope

The two main theorem statements are unchanged. CriticalDepth.ReviewV2.nativeTheoremOne_proved covers finite-dimensional subsystem codes, detection of every supported operator below d, and one total circuit-depth budget; it proves finiteness and non-density of the exact projective logical image. CriticalDepth.ReviewV2.standardTheoremTwo_proved covers ordinary qubit stabilizer codes of actual distance d with trivial gauge subsystem; it proves the sharp critical-depth equality and a nontrivial closed subgroup isomorphic to Circle.

The revised article now presents the same algebraic proof mechanism used in Lean: independent matrix and inverse variables, both encoding relations, scalar extension of detection, two-sided support propagation, a scalar logical logarithmic derivative, and finite joint evaluations of logical conjugation coordinates. The global algebraic step passes to minimal-prime fraction fields, proves constants there, and uses Noetherianity and integrality. The coordinate algebra is not assumed reduced or zero-dimensional. No CAD proof is used in the revised article.

The End Matter component-count inequality, affine Bezout estimate, explicit parameter bound, tensor-power observation, and proposed elimination/unitary-feasibility procedure are additional written deductions. They have not been formalized or executed in the cited Lean development. The literature discussion and fault-tolerance commentary also remain outside the two named formal interfaces.

## Source and execution evidence

The Lean source remains byte-identical to the cleanly replayed proof snapshot 411ff86bd30e423b3bc15267006e7bb3b409506d, with SHA-256 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2. Its recorded recursive dependencies contain no project axioms or sorryAx; the two main theorem axiom sets are propext, Classical.choice and Quot.sound. No new Lean execution is claimed for this prose revision. The existing receipt binds its original manuscript and documentation; RELEASE_BINDING.json records the revised article and changed documentation separately.

The original author approval is preserved with its original input hash. The user separately requested this proof rewrite and repository synchronization. No extension of that historical approval or kernel coverage to the new quantitative discussion is asserted.

## Bibliographic check

The Bonet-Monroig entry remains unchanged: X. Bonet-Monroig, R. Sagastizabal, M. Singh and T. E. O'Brien, Low-cost error mitigation by symmetry verification, Physical Review A 98, 062339 (2018), DOI 10.1103/PhysRevA.98.062339, arXiv:1807.10050. Section IV and Figure 2(a) describe an in-line symmetry-verification circuit with binary-tree connectivity and logarithmic depth. The article cites its unitary parity-concentration part; the general arity and exact depth formula are derived in the article.
