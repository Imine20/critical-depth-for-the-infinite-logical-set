# Historical 47-module development

This development is historical. Its original complete release is [c7e9b4591c43c266947152b454f2008b12dc9f4c](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/c7e9b4591c43c266947152b454f2008b12dc9f4c), with primary code commit `e882b1bd36838b3f825d35f07d9d4b46a5d3357b` and manuscript SHA-256 `18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85`.

The previous root's 47-module source files, original entry and saved records are preserved without byte changes in the [complete preceding-main snapshot](../previous-main-5c602/). That snapshot retains the version-clarification notices already present at `5c602e32c66547a183f555e8c963e4621709fc90`; it does not turn the historical project into acceptance of the current manuscript.

For historical reproduction, create a separate checkout of the original release and follow its original instructions:

~~~sh
git checkout --detach c7e9b4591c43c266947152b454f2008b12dc9f4c
lake exe cache get
lake env sh scripts/verify.sh
~~~

The current repository root instead registers only `CriticalDepthMathlib`, sourced from `mathlib-review/CriticalDepthMathlib.lean`. The historical files are absent from the current build entry. The current source, current consumer, current reports and their dependency pins are documented at the root. A version mismatch is an applicability boundary, not a new mathematical counterexample.
