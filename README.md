# Critical depth for the infinite logical set

The portable [Mathlib verification package](mathlib-review/README.md) contains
the [complete Lean proof](mathlib-review/CriticalDepthMathlib.lean), readable
[mathematical statements](mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md),
the [three-layer correspondence](mathlib-review/THREE_LAYER_CORRESPONDENCE.md),
and [responses to the audit](mathlib-review/AUDIT_RESPONSE.md).

The bound Lean 4.35.0 source passed the recorded kernel build and recursive
axiom checks: 1,251 theorem declarations, 1,727 mathematical constants and
29 registered targets. The [public mathematical audit](mathlib-review/KERNEL_AUDIT.txt)
retains every recursive record and all target types. The
[selected verification summary](mathlib-review/VERIFICATION.json) states the
version pins, source binding, exact scope and trust boundary. Author semantic
approval remains **PENDING**.

Download the [portable ZIP](mathlib-review/critical_depth_mathlib_review_lean435.zip)
and follow its README to reproduce the check with pinned public dependencies.
The [manuscript PDF](manuscript/shallow_logical_operators_depth_threshold.pdf)
and [TeX source](manuscript/shallow_logical_operators_depth_threshold.tex)
are included. The formal finiteness proof uses an alternative algebraic route;
the written CAD proof is not checked line by line. These are scoped formal
results, not certification of every claim in the paper.

This referenced release includes portable mathematical evidence and excludes
local execution diagnostics. The proof and manuscript bytes are unchanged by
this packaging revision; it does not represent a new Lean run or independent
fresh-clone replay. Timestamp receipts attest only their own listed bytes.
