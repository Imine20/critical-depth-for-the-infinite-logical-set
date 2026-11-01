# Verification versions and evidence scope

The current proof entry is the [portable Mathlib package](mathlib-review/README.md).
The older records under docs/ and verification/ describe a different manuscript
snapshot. Their applicability to the present manuscript is **VERSION_MISMATCH**.
This classification preserves the historical successful run; it does not report
a new Lean failure.

This index classifies the repository state at commit
[d0e1eb1cfdd58d4d0bad97ee58d9b121ca55117e](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/commit/d0e1eb1cfdd58d4d0bad97ee58d9b121ca55117e).
The correction changes documentation and classification metadata only.

## Current entry and historical entry

| Record | Bound manuscript | Scope and applicability |
| --- | --- | --- |
| [mathlib-review](mathlib-review/README.md) | 98e19ea5…41919227 | Current portable single file; recorded v2-033 audit: 1,251 theorem declarations, 1,727 mathematical constants, 29 targets |
| [Legacy root verification](verification/README.md) | 18efaf29…634bf85 | Historical 47-module run, 972 theorem declarations, 1,296 mathematical constants and seven targets; VERSION_MISMATCH against the present manuscript |
| [Selected editorial baseline](mathlib-review/THREE_LAYER_CORRESPONDENCE.md) | 118b256b…bc380a1c | Provenance for the derived current manuscript, not a byte-identical copy or an independent proof |

Current TeX SHA-256:

~~~text
98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227
~~~

Current PDF SHA-256:

~~~text
e5e5157b590a93c26fe5d5b99ac5fdacc3e34a2229493ea88ce9eaff2fcfcbde
~~~

Current Lean source SHA-256:

~~~text
85af30d2f9cdf217a729c004d7af0ad67f87b4a821eb28e38ae70dfec840dfd8
~~~

The current manuscript adds the explicit empty-support scalar-phase convention
to its selected editorial baseline. It is a derived version, not a verbatim
copy of that baseline. Its stored mathematical audit remains the record of
the accepted v2-033 build. Hash checks made during this correction are static
binding checks; they are not a new build or dynamic axiom audit.

## Why the old inventory does not verify the present manuscript

The unchanged [53-row historical manifest](verification/source-manifest.sha256)
has SHA-256 cdb7bde150cadbaa6e10ba24b1f38be560c582331d4385fb50b0486a1202b4a8.
At the classified repository state, 52 input hashes match and the sole mismatch
is the manuscript TeX: the manifest expects 18efaf…bf85, while the present file
is 98e19…19227. [Machine-readable classification](verification/source-manifest.status.json)
records the full hashes and scope. The old expected hash has not been replaced.

[Legacy results](verification/results.json),
[legacy manuscript binding](verification/manuscript-binding.json), and
[legacy PDF QA](verification/pdf-qa.json) preserve their original data inside
explicit historical records. Their top-level VERSION_MISMATCH status refers
to applicability to today's manuscript. A PASS inside a nested historical
record retains its original, historical meaning.

All legacy material in docs/ and verification/, including the two theorem
proof narratives and saved audit/type outputs, is scoped to that historical
release unless explicitly identified as a classification notice.
The unmodified originals are available at the immutable
[legacy release c7e9b4591c43c266947152b454f2008b12dc9f4c](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/c7e9b4591c43c266947152b454f2008b12dc9f4c).
Its primary code commit is
[e882b1bd36838b3f825d35f07d9d4b46a5d3357b](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/tree/e882b1bd36838b3f825d35f07d9d4b46a5d3357b).

## Reproduce the current check

~~~sh
cd mathlib-review
lake exe cache get
sh verify.sh
~~~

The root Lake project and scripts/verify.sh remain the legacy 47-module
development. Their results must be read with their own fresh input inventory.
They do not replace the current package's embedded 29-target audit.

## Timestamp and interpretation boundaries

The old [76-file timestamp collection](timestamps/README.md) belongs to its
immutable legacy release. Verify those bytes in that historical checkout;
do not apply its PASS to paths revised in later commits.

The current [20-file timestamp collection](mathlib-review-timestamps/README.md)
binds the portable proof package and current manuscript. All 20 primary files,
all 23 current timestamp evidence files, the portable ZIP, and all old timestamp
files are unchanged by this correction. These new classification notices are
outside both stamped collections; no new timestamp is claimed for them.

The readable mathematical statements expose the formal definitions; they are
not an additional independent proof. The closed Circle subgroup is an explicit
strengthening of the manuscript's continuous-subgroup conclusion. The formal
finiteness proof follows an alternative algebraic route and does not verify
the written CAD argument step by step. Author semantic approval remains PENDING.
