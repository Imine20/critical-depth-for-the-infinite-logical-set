# Standard Pauli stabilizer correspondence

> GitHub reading edition of the [recorded source](../../mathlib-review/STABILIZER_DEFINITION_CORRESPONDENCE.md). The status statements below refer to that earlier review. See the [v7 verification status](../../VERIFICATION_STATUS.md) for the current record.

Current integrated source: SHA-256 3c90628e5567d329989aacf62e8216776e23eee508ae789d563f579f250d7ff2. Its completed main build, recursive audit and actual caller are recorded separately. The latest user-supplied manuscript has SHA-256 1c17ca04507174ce6b070af71a898626e279668d598d04b8b052787481d9ba0d; see [the manuscript correspondence](../LATEST_MANUSCRIPT_CORRESPONDENCE.md) for its notation and standard-subspace scope. The older manuscript and imported-source hashes below describe the supplement's development provenance. Author approval remains PENDING.
This supplement addresses the stabilizer-code definition used by Theorem 2.
It does not change the manuscript or attempt its deferred CAD proof route.
The supplement passed a controlled Lean 4.35.0 development compilation. All nine registered target axiom outputs were exactly the standard three; a separate full inventory accepted 15 theorems and 20 mathematical constants with zero own axioms. The finite-subgroup supplement also compiled with the standard three. These development runs used the previously checked public dependency cache. Final integrated acceptance uses the pinned trusted Mathlib cache, as requested by the user, and is recorded separately by exact source hash.
This correspondence is not an author attestation; consult the separately version-bound author-approval record.

The imported source is `CriticalDepthMathlib.lean`, SHA-256
`85af30d2f9cdf217a729c004d7af0ad67f87b4a821eb28e38ae70dfec840dfd8`.
The development-reference manuscript TeX has SHA-256
`98e19ea527d1c6caff7b06debace8a03790fb57126bbe9754bc89d8341919227`.
The supplement imports that unchanged compiled-source interface; it does not
relabel a historical verification receipt as acceptance of its new statements.

## Independent standard definition

Gottesman's *Stabilizer Codes and Quantum Error Correction*, Section 3.2,
printed pages 18–19, describes an abelian Pauli subgroup and defines its coding
space as the entire space fixed by that subgroup. Its scalar-phase exclusions
ensure that the coding space is nonzero. The same section records the
Pauli-specific commute-or-anticommute property. See the
[primary thesis](https://arxiv.org/pdf/quant-ph/9705052#page=26).

The supplement spells out the following definition without invoking
`NativeStabilizer`:

1. A Pauli matrix has entries
   $`A_{x,y}=z\prod_i(p_i)_{x_i,y_i}`$, with
   $`z\in\{1,-1,i,-i\}`$ and each $`p_i`$ one of the explicit matrices
   $`I,X,Y,Z`$. Here $`Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}`$.
2. $`S`$ is a Mathlib `Subgroup` of
   `Matrix.unitaryGroup (QubitBasis n) ℂ`. Every member is such a Pauli matrix,
   every two members commute, and the actual unitary matrix $`-I`$ is absent.
3. The encoding range is **equal to**, rather than merely contained in,
   $`\{v:\;Uv=v\text{ for every }U\in S\}`$.

The definitions are `StandardPauliOperator`, `StandardPauliSubgroup`, and
`StandardStabilizerCode` in namespace `CriticalDepth.ReviewV2`.
The four-constructor `SinglePauli` labels concrete matrices; it does not
replace a general group, vector-space, or Hilbert-space carrier. The group,
matrix, complex-number, function-space, and subgroup carriers are Mathlib's.
The tensor-product entries use the full computational basis
`QubitBasis n = ((i : Fin n) → Fin 2)`.

An ambient unitary subgroup whose members all belong to this explicit Pauli
set is precisely a subgroup of the Pauli matrices in this representation.
The supplement does not separately package that finite set as a second
ambient bundled group or prove its cardinality formula.

## Why the two definitions agree

The existing `NativeStabilizer` asserts a Pauli subgroup and the same
whole-fixed-space equality. It does not explicitly assert commutativity or
the absence of $`-I`$. The new forward implication proves both properties.

Let $`V^\dagger V=I`$. The domain of $`V`$ is
`Fin (2 ^ k) × Fin 1`, which has a coordinate for every natural $`k`$, including
$`k=0`$. Consequently $`V\ne -V`$: multiplying that equation by
$`V^\dagger`$ would give $`I=-I`$, contradicted by a diagonal entry.
No hypothesis $`n>0`$, $`k>0`$, a distance bound, or a chosen nonzero codeword
is added to this definition bridge.

The whole-fixed-space equality gives $`UV=V`$ for every subgroup member.
For two Pauli members $`U,W`$, the existing tensor-matrix theorem proves
$`UW=WU`$ or $`UW=-WU`$. The second case gives
$`V=(UW)V=-(WU)V=-V`$, which is impossible. Thus they commute.
If $`-I`$ were a member, its equation $`(-I)V=V`$ would yield the same
contradiction. The converse implication simply retains the Pauli condition
and whole-fixed-space equality.

A separate lemma proves the stronger scalar statement: if a subgroup member
is $`zI`$, then $`z=1`$. Compress $`(zI)V=V`$ by $`V^\dagger`$ and inspect a
diagonal entry of $`zI=I`$. In particular, the imaginary scalar phases cannot
belong to the subgroup either. This proof requires neither a cardinality
theorem nor an assumed trace identity.

## Correspondence and new theorem endpoint

| Mathematical claim | Lean declaration | Status or difference |
| --- | --- | --- |
| The explicit four phases give the usual Pauli matrices | `isPauli_iff_standardPauliOperator` | Development proof accepted by the four phase cases and matrix extensionality; independent of any code definition. |
| The native subgroup is abelian and excludes $`-I`$ | `pauli_subgroup_with_encoding_is_standard` | Development proof accepted; derivation from the original isometry and whole-fixed-space premises. These properties are not supplied as new assumptions. |
| A scalar stabilizer member has scalar one | `scalar_member_of_stabilizer_eq_one` | Development proof accepted; derivation for every complex scalar. |
| Standard and native stabilizer-code definitions agree | `nativeStabilizer_iff_standard` | Two-way bridge under $`V^\dagger V=I`$, already required by the main theorem. |
| The same definition agrees with the original internal code representation | `standardStabilizer_iff_legacy` | Composition with the existing raw-matrix/internal-code bridge. |
| The full critical-depth and closed-circle conclusion for the standard definition | `StandardTheoremTwo`, `standardTheoremTwo_proved` | Same $`n,k,d,q,V`$, $`k\ge1,d\ge2,q\ge2`$, isometry, and actual-distance hypotheses as `NativeTheoremTwo`; only its stabilizer predicate is replaced using the proved bridge. |
| A concrete standard-code instance and a call of the new main theorem | `StandardExamples.fourQubit_standardStabilizer`, `StandardExamples.fourQubit_standard_critical_circle` | Uses the existing actual [[4,2,2]] encoding, stabilizer proof, and distance proof. No code-existence hypothesis is introduced. |

The standard-version main theorem retains equality of the first positive
depth budget permitting infinitely many logical classes with
$`2\lceil\log_q d\rceil-1`$. It also retains an actual nontrivial closed
Mathlib subgroup of the native projective unitary group, a topological group
isomorphism from `Circle`, and containment in the logical image at that common
total budget. The Pauli generator is still derived by the existing main proof;
it is not an additional premise of this corollary.

All new declarations must pass the existing recursive axiom gate: only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The source includes
recursive axiom print commands for the bridge, scalar lemma, main corollary,
and actual-code calls. These targets passed the controlled development build and axiom checks; the combined supplement inventory accepted all 23 mathematical constants, 18 theorem declarations and 12 exact-three targets with zero own axioms. The final integrated source-based acceptance belongs to its separate version-bound verification record.

The supplement proves no separate formula $`|S|=2^{n-k}`$, classification of
all abstract stabilizer groups, or new general Hilbert-space tensor transport.
Those assertions are not hidden in its predicates or used as premises.
The already delivered Hilbert-coordinate transport remains a separate bridge.
No conclusion here constitutes version-bound author approval of the paper's
semantics.
