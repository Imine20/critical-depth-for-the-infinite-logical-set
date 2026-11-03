# Current manuscript and Lean scope

The two main theorem environments are unchanged from publication e199f3338e29ba3d8fbda5212f3a865af0b41d3a. Theorem 1 retains the finite-dimensional subsystem-code setting, all-operator detection below d, one total circuit-depth budget and the strict depth inequality. Theorem 2 retains ordinary qubit stabilizer codes with trivial gauge subsystem and actual distance d. No intermediate code-preservation or geometry assumption has been added.

The article's Theorem 1 proof and algebraic finite-image lemma now follow the route in the existing Lean source. Independent review checked the formal inverse presentation, both encoding relations, extension of detection, two-sided light cones, common-frame compression, vanishing derivations, minimal-prime constants, nilpotents and finite joint evaluations. The revised Figure 1 uses derivations and inverses rather than analytic path derivatives and adjoints.

The parameter and exact-counting discussion is in End Matter. Its component-count inequality, numerical bound and algorithmic observations are additional mathematical deductions, not formal claims in the current source. No new Lean build or numerical enumeration is asserted.

The immutable original approval and clean-replay records keep their own input hashes. RELEASE_BINDING.json binds the new article and distinguishes unchanged proof inputs from revised prose and scope documents. The prior detailed comparison remains in the earlier publication commit; this revision does not add a step-by-step correspondence table.
