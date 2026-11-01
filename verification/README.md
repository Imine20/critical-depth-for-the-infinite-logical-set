# Legacy verification records

**Historical scope: VERSION_MISMATCH against the present manuscript.**
These records describe the 47-module verification of manuscript SHA-256
18efaf2918080dc29eaf5ef1d76838a4117029df0ee9cd2e069aba41e634bf85
at [legacy release c7e9b4591c43c266947152b454f2008b12dc9f4c](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/c7e9b4591c43c266947152b454f2008b12dc9f4c).

The manuscript now stored at the same root path has SHA-256
98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227.
Use the [current Mathlib package](../mathlib-review/README.md),
[current verification summary](../mathlib-review/VERIFICATION.json), and
[version index](../VERIFICATION_STATUS.md) for that release.

| File or group | Meaning |
| --- | --- |
| results.json | Explicit historical result wrapper; original PASS applies to its old input set |
| manuscript-binding.json | Historical manuscript provenance; not a verbatim binding of the present TeX |
| pdf-qa.json | QA for the old PDF hash; not a new visual inspection of the present PDF |
| source-manifest.sha256 and replay-source-inputs.sha256 | Unchanged 53-row historical input lists |
| source-manifest.status.json | Static classification of the saved list against the classified current checkout |
| audit.txt, expanded-main-types.txt, origin lists and other saved outputs | Historical seven-target audit and replay evidence |
| AuxiliaryCalls.lean | Legacy root-project consumer, not the native integrated 29-target entry |

The unchanged old manifest has 52 matches and one manuscript mismatch at the
classified commit. A recorded historical source-binding PASS does not turn
that old manifest into a current-version verification. The original documents
and result bytes remain available at the pinned historical commit.

For the current check, run from the repository root:

~~~sh
cd mathlib-review
lake exe cache get
sh verify.sh
~~~

To replay the historical root development, use a separate checkout pinned to
the legacy release and its own instructions. The root script inventories the
inputs of a new run; it does not check the saved 53-row list or replay the native
29-target package.

The old 76-file timestamps require the historical checkout. The newer 20-file
timestamps cover only their listed portable release. This classification
correction changes neither signed collection and claims no new Lean build,
dynamic axiom audit, PDF rendering or timestamp. Author semantic approval
remains pending; the manuscript CAD proof is a separate written proof route.
