# Algebraic proof route in the revised manuscript

The manuscript now presents the coordinate-algebra and derivation route used by CriticalDepthMathlib.lean. The former smooth-cell/CAD proof has been removed. This file retains its historical filename to preserve existing links; no step-by-step correspondence table is provided.

For each finite support arrangement, the coordinate algebra uses local forward and inverse matrix entries and logical and gauge matrix pairs. It imposes both UV = V(W tensor Z) and EU = (W tensor Z)E, where E is the constant complex matrix V adjoint. Physical unitary circuits supply evaluations; generic extension-field points are invertible algebraic solutions and are not assumed unitary.

Detection extends to extension fields by linear span. The two-sided light cones and both encoding relations give gauge-only compression in a common frame. Every complex-linear field derivation then annihilates the logical conjugation coordinates. Minimal-prime fraction fields make these coordinates constants; Noetherianity and nilpotence produce global monic polynomial relations, yielding finite joint evaluations. Conjugation separates physical unitaries modulo phase.

The revised End Matter proves this finite-image lemma and separately discusses component counts, a coarse Bezout bound and exact-counting feasibility. The latter quantitative material is not present as a cardinality theorem or algorithm in the Lean source. The main source, theorem interfaces and toolchain are unchanged; the prior clean-replay evidence retains its original byte bindings. See ../docs/LEAN_SCOPE_AND_CITATION_NOTE.md and ../RELEASE_BINDING.json for current scope and provenance.

The older manuscript and route comparison remain available in publication commit e199f3338e29ba3d8fbda5212f3a865af0b41d3a. Historical receipts and author-approval files have not been rewritten.
