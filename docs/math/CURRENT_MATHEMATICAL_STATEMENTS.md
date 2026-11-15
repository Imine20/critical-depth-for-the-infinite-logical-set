# Current mathematical statements

This specification states the definitions, quantifiers and mathematical claims of [Update_branch.tex](../../manuscript/Update_branch.tex), including the three main theorems and the supporting propositions used in their correspondence with Lean. It was extracted from the current manuscript and checked against the Lean definitions and theorem interfaces. It is not an independently authored historical specification or an author-approval record. The older [aligned statements](ALIGNED_MATHEMATICAL_STATEMENTS.md) and [original statements](ORIGINAL_PURE_MATHEMATICAL_STATEMENTS.md) retain their earlier scope.

The [current three-layer correspondence](../CURRENT_THREE_LAYER_CORRESPONDENCE.md) records manuscript labels, these stable section identifiers, fully qualified Lean declarations and the limits of each comparison. Source hashes, dependency versions and actual execution results belong to the version and replay records linked there. This document does not itself certify a build or a line-by-line verification of the manuscript's proofs.

Throughout, the gate arity is written as $\rho$; Lean generally calls it `q`. All Hilbert spaces are over $\mathbb C$. All dimensions and circuit budgets are finite integers unless a threshold or exponent is explicitly allowed to take the value $\infty$.

<a id="s1"></a>
## S1. Physical systems, encoding, support and distance

Let $n\ge1$, $K\ge2$ and $g\ge1$. Let $\mathcal H_i$ be finite-dimensional complex Hilbert spaces and set

```math
\mathcal H=\bigotimes_{i=1}^{n}\mathcal H_i,
\qquad \dim\mathcal H_L=K,
\qquad \dim\mathcal H_G=g.
```

An encoding is a linear isometry

```math
V:\mathcal H_L\otimes\mathcal H_G\longrightarrow\mathcal H,
\qquad V^\dagger V=I_{L\otimes G}.
```

An operator $O$ is supported on $S\subseteq\{1,\ldots,n\}$ if, after the canonical rearrangement of tensor factors, it is $O_S\otimes I_{S^c}$ for some arbitrary complex linear operator $O_S$. It need not be Hermitian, unitary or Pauli.

For an integer $d\ge2$, define detection below $d$ by

```math
\operatorname{DetectsBelow}(V,d)\iff
\forall S\ (|S|<d)\ \forall O\text{ supported on }S,
\quad \exists M_O\in\operatorname{End}(\mathcal H_G),
\quad V^\dagger O V=I_L\otimes M_O.
```

The witness $M_O$ may depend on $O$. Actual distance $d$ means detection below $d$ together with

```math
\exists S\ (|S|=d)\ \exists O\text{ supported on }S,
\quad \forall M\in\operatorname{End}(\mathcal H_G),
\quad V^\dagger O V\ne I_L\otimes M.
```

Thus a distance lower bound and an attained actual distance are different hypotheses. Theorem 1 uses the former; the stabilizer onset and fault-suppression sharpness results use the latter.

A qubit stabilizer subspace code has $\mathcal H=(\mathbb C^2)^{\otimes n}$, $K=2^k$ with $k\ge1$, and $g=1$. Its encoding range is the entire common $+1$ eigenspace of an abelian subgroup $S$ of the $n$-qubit Pauli group, with $-I\notin S$. The Pauli group consists of tensor products of $I,X,Y,Z$ multiplied by a phase in $\{1,-1,i,-i\}$. The entire-fixed-space condition is part of the definition; an arbitrary proper subspace of that fixed space does not satisfy this definition merely because the stabilizers fix it.

Relevant definitions include `CriticalDepth.ReviewV2.NativeDetectsBelow`, `NativeActualDistance` and `StandardStabilizerCode`, and `CriticalDepth.Manuscript.DetectsBelow`, `HasActualDistance` and `IsStabilizer`. Their representation bridges are recorded in the correspondence table.

<a id="s2"></a>
## S2. Native circuits, exact logical actions and the phase quotient

Fix $\rho\ge2$. A native gate is an arbitrary unitary on any support of at most $\rho$ physical factors, extended by the identity outside that support. A layer is a finite list of native gates whose supports are pairwise disjoint. A circuit of depth at most $h$ has $r$ layers for some $0\le r\le h$, and its unitary $U$ is the ordered product of all gates. The model allows every support arrangement and every such unitary matrix. It has no geometric locality restriction or finite gate alphabet. It uses the original register, without ancillary systems, measurements, resets, adaptive steps or code changes.

The complete circuit implements an exact logical action if

```math
\exists W\in U(\mathcal H_L)\ \exists Z\in U(\mathcal H_G),
\qquad UV=V(W\otimes Z).
```

This equation holds for all logical and gauge states. It does not require each gate or intermediate layer to preserve the code. The logical action is the class $[W]$ in

```math
PU(K)=U(K)/\{zI_K:z\in\mathbb C,\ |z|=1\},
```

equipped with its quotient group topology, equivalently its usual compact Lie-group topology. The quotient identifies one global phase. Positive logical and gauge dimensions and the isometry condition make the logical factor unique up to that phase.

Write

```math
\mathcal L_{\le h}(V;\rho)=
\{[W]:\exists r\le h\ \exists\text{ allowed depth-}r\text{ circuit }U
\ \exists Z\in U(g),\ UV=V(W\otimes Z)\}.
```

Every member has its own complete circuit within the same total depth budget. This set is increasing in $h$ and is closed under inverses, but need not be closed under products. Depth zero gives only the projective identity. Empty-support gates are scalar phases; they can be removed without changing the projective logical image. The noise convention for these gates is stated separately in S6.

The fixed-partition transversal finiteness statement used for context concerns exact actions respecting one partition into detectable blocks, modulo global phase. Allowing arbitrary undetectable blocks or retaining all scalar phases would change that statement.

Relevant definitions are `CriticalDepth.ReviewV2.NativeGateData`, `NativeLayer`, `NativeCircuit`, `NativeCircuitAllowed`, `nativeLogicalImage`, `scalarPhaseSubgroup` and `PU`.

<a id="s3"></a>
## S3. Algebraic finite-image criterion and Theorem 1

### Algebraic finite-image criterion

Let $R$ be a finitely generated commutative unital $\mathbb C$-algebra, and let $r_1,\ldots,r_m\in R$. For each minimal prime ideal $\mathfrak p$ of $R$, set

```math
F_{\mathfrak p}=\operatorname{Frac}(R/\mathfrak p),
\qquad \iota_{\mathfrak p}:R\longrightarrow F_{\mathfrak p}.
```

Assume

```math
\forall\mathfrak p\in\operatorname{MinSpec}(R)\quad
\forall\delta\in\operatorname{Der}_{\mathbb C}(F_{\mathfrak p},F_{\mathfrak p})\quad
\forall i\in\{1,\ldots,m\},
\qquad \delta(\iota_{\mathfrak p}(r_i))=0.
```

Then the joint evaluation image

```math
\{(\phi(r_1),\ldots,\phi(r_m)):
\phi:R\longrightarrow\mathbb C\text{ a unital }\mathbb C\text{-algebra map}\}
```

is finite. Each minimal prime contributes at most one joint output tuple. The zero algebra has no such evaluation and gives the empty image. Reducedness, smoothness and a zero-dimensional parameter variety are not required. The derivations are taken in the component function fields, before evaluation at complex points.

The Lean endpoint is `CriticalDepth.Manuscript20261114.finiteEvaluationImage`; `evaluationImage_encard_le_minimalPrimes` records the component-count bound.

### Theorem 1: finiteness below the distance threshold

For integers $\rho,d\ge2$, put

```math
H(\rho,d)=2\lceil\log_\rho d\rceil-1.
```

For every encoding in S1 satisfying $\operatorname{DetectsBelow}(V,d)$ and every integer $h\ge1$,

```math
h<H(\rho,d)
\quad\Longrightarrow\quad
\mathcal L_{\le h}(V;\rho)\text{ is finite}
\quad\text{and}\quad
\overline{\mathcal L_{\le h}(V;\rho)}\ne PU(K).
```

No stabilizer assumption is present. The conclusion is for each encoding and budget; it does not assert a uniform finite cardinality across code families. It also does not assert that the group generated by this finite set is finite or nondense.

When $\rho\ge d$, $H(\rho,d)=1$, so no positive $h$ satisfies the strict inequality. For $d>\rho$, the excluded positive depths are $1\le h\le H(\rho,d)-1$. Non-density uses the actual Hausdorff quotient topology and $K\ge2$, not just finiteness in an arbitrary topological space.

The endpoints are `CriticalDepth.ReviewV2.nativeTheoremOne_proved` and `CriticalDepth.ReviewV2.HilbertCircuitTransport.theoremOne_arbitrary_carriers`. In the latter, the coordinate transport preserves supports and the full logical image in both directions.

<a id="s4"></a>
## S4. Positive onset and the stabilizer circle: Theorem 2(1)

For the encoding and gate model in S1–S2, define

```math
h_\infty(V;\rho)=
\min\{h\in\mathbb Z_{\ge1}:\mathcal L_{\le h}(V;\rho)\text{ is infinite}\},
```

with the minimum of an empty set defined as $\infty$. Lean expresses this threshold as an infimum in $\mathbb N\cup\{\infty\}$ and proves the finite-budget characterization. The positive budget convention still includes zero-depth circuits in each $\mathcal L_{\le h}$.

For every qubit stabilizer subspace code of S1 with actual distance $d\ge2$, and every $\rho\ge2$,

```math
h_\infty(V;\rho)=H(\rho,d).
```

At this budget, the realizable set contains a nontrivial continuous one-parameter subgroup. More explicitly, there is one nonscalar logical Hermitian involution $A$, with $A^\dagger=A$ and $A^2=I$, such that

```math
F_A(t)=e^{itA}=\cos(t)I+i\sin(t)A,
\qquad [F_A(t)]\in\mathcal L_{\le H(\rho,d)}(V;\rho)
\quad\text{for every }t\in\mathbb R.
```

The map $t\mapsto[F_A(t)]$ is a continuous group homomorphism. The strengthened formal witness has projective kernel $\pi\mathbb Z$; its image is a closed nontrivial subgroup topologically group-isomorphic to the unit circle. The same $A$ supplies the family and its circuit implementations. Special angles may admit shallower circuits; the threshold does not give a lower bound for each individual angle.

The code, encoding and all angles use the same native gate model as Theorem 1. The minimum-weight physical logical Pauli and its synthesis are derived from the stabilizer and actual-distance hypotheses. They are not extra premises.

The endpoints include `CriticalDepth.ReviewV2.standardTheoremTwo_proved` and `CriticalDepth.ReviewV2.critical_circle_joint_witness`.

<a id="s5"></a>
## S5. Dense and exact generation: Theorem 2(2)

Define the algebraically generated subgroup

```math
G_h(V;\rho)=\langle\mathcal L_{\le h}(V;\rho)\rangle\le PU(K).
```

Its elements are finite words in the realizable set; inverses are already available by circuit reversal. Define

```math
\begin{aligned}
h_{\rm dense}(V;\rho)
 &=\min\{h\in\mathbb Z_{\ge1}:\overline{G_h(V;\rho)}=PU(K)\},\\
h_{\rm exact}(V;\rho)
 &=\min\{h\in\mathbb Z_{\ge1}:G_h(V;\rho)=PU(K)\}.
\end{aligned}
```

Both empty-set minima are $\infty$, and the closure is topological closure in $PU(K)$. These thresholds bound each generator's implementing circuit. A word of $r$ depth-at-most-$h$ generators has total depth at most $rh$; no uniform bound on $r$ is asserted here.

For every finite-dimensional subsystem encoding of S1 and every $\rho\ge2$,

```math
h_{\rm exact}(V;\rho)
=\max\{h_\infty(V;\rho),h_{\rm dense}(V;\rho)\}.
```

This equality includes infinite thresholds. It needs neither detection nor a stabilizer hypothesis. Under detection below $d\ge2$, Theorem 1 additionally gives $h_{\rm exact}\ge h_\infty\ge H(\rho,d)$. It gives no corresponding lower bound on $h_{\rm dense}$: a finite set can generate a dense subgroup.

The final Lean endpoint is `CriticalDepth.ReviewV2.nativeExactDepth_eq_max`. Its hypotheses are the isometry equation, $K\ge2$ and $g\ge1$; the code establishes the curve and identity-neighborhood steps internally. The manuscript's semialgebraic-stratum argument and the formal real-algebraic/local-flow argument are different proof routes to this statement.

<a id="s6"></a>
## S6. Fault histories, recovery, metrics and exponents

The fault-suppression statements use qubit subspace codes, with $g=1$, ideal encoding and ideal terminal recovery. An admissible noiseless circuit is a finite native gate list of S2 with exact logical action. Every occurrence with nonempty support is a noisy location, even if its unitary is the identity. Empty-support scalar gates are not noisy locations. Distinct occurrences of the same gate remain distinct locations. There is no implicit idle-qubit noise; such a location must appear as a gate in the list.

Let $\mathrm{Loc}$ be this finite set of locations. For each $j$, let $\mathcal P_j^*$ be all nonidentity phase-free Pauli strings on that gate's support. Choose constants

```math
a_{j,P}>0,
\qquad \sum_{P\in\mathcal P_j^*}a_{j,P}=1,
```

independent of the noise parameter $p$. At each location, independently, apply $I$ after the ideal gate with probability $1-p$, or $P\in\mathcal P_j^*$ with probability $p\,a_{j,P}$. A history $x$ chooses one of these outcomes at every location. If $f(x)$ is its number of faults and $N_{\rm loc}=|\mathrm{Loc}|$, its probability is

```math
\Pr_p(x)=p^{f(x)}(1-p)^{N_{\rm loc}-f(x)}
\prod_{j\text{ faulty in }x}a_{j,x_j}.
```

All circuit, code and weight parameters are held constant when $p\to0^+$. Constants in asymptotic bounds may depend on them. The complete history is unobserved. Propagation through arbitrary native unitaries need not leave a Pauli channel at the output.

A recovery $\mathcal R$ is one CPTP map from the physical output to the logical system, including decoding. The same map acts on every history in the mixture. It may depend on the code, circuit, noise law and $p$, and may use syndrome information; it cannot use the unknown logical input or the unobserved history. The allowed recovery is an ideal channel, not a prescribed decoder or a noisy recovery circuit.

For intended logical unitary $W$, let $\mathcal M_{\mathcal R,p}$ be the noisy encoded-and-recovered channel, and put

```math
\Lambda_{\mathcal R,p}=\mathcal W^{-1}\circ\mathcal M_{\mathcal R,p},
\qquad \mathcal W(\sigma)=W\sigma W^\dagger.
```

With $|\Phi_K\rangle=K^{-1/2}\sum_{j=1}^K|j\rangle|j\rangle$ and $\Phi_K=|\Phi_K\rangle\langle\Phi_K|$, define

```math
\begin{aligned}
\epsilon(\mathcal R,p)
 &=1-\langle\Phi_K|({\rm id}\otimes\Lambda_{\mathcal R,p})(\Phi_K)|\Phi_K\rangle,\\
r_{\rm av}(\mathcal R,p)
 &=\int\bigl[1-\langle\psi|\Lambda_{\mathcal R,p}(|\psi\rangle\langle\psi|)|\psi\rangle\bigr]\,d\psi,\\
\delta(\mathcal R,p)
 &=\tfrac12\|\Lambda_{\mathcal R,p}-{\rm id}\|_\diamond.
\end{aligned}
```

The integral is Haar measure on pure logical states; the diamond norm is the completely bounded trace norm. Optimize each metric separately over all terminal CPTP maps, writing $\epsilon^{\rm opt}$, $r_{\rm av}^{\rm opt}$ and $\delta^{\rm opt}$. Lean defines these quantities as infima and proves attainment for the entanglement and diamond metrics in this finite-dimensional setting for $p\in[0,1]$. The proportionality below gives attainment for average infidelity. The Kraus/CPTP representation equivalence is also proved. The three metrics need not share an optimizer.

For every recovery and every valid $p$,

```math
r_{\rm av}(\mathcal R,p)=\frac{K}{K+1}\epsilon(\mathcal R,p),
\qquad \epsilon(\mathcal R,p)\le\delta(\mathcal R,p).
```

The proportionality also holds after minimization. For an effective physical Pauli channel, syndrome probabilities $q_{s,\ell}$ give the specialization

```math
\epsilon^{\rm opt}(p)=1-\sum_s\max_\ell q_{s,\ell}(p).
```

That specialization is not assumed for general native circuits.

For an optimized error function $e(p)$, define its integer exponent by

```math
\operatorname{ord}(e)=
\sup\{m\in\mathbb N:e(p)=O(p^m)\text{ as }p\to0^+\}
\in\mathbb N\cup\{\infty\}.
```

For each metric $e$, define the per-code exponent

```math
m_{\rm pc}^{e}(\mathcal C;\rho,h)
=\inf_{(L,a)}\operatorname{ord}(e^{\rm opt}_{L,a}),
```

where $(L,a)$ ranges over all exact code-preserving circuits of depth at most $h$ and all strictly positive, normalized, $p$-independent conditional Pauli laws on their noisy locations. The infimum is in $\mathbb N\cup\{\infty\}$, with empty infimum $\infty$. A finite infimum is attained. S7 shows that for each gate list its exponent is independent of the positive law, so suppressing the law in the manuscript's notation does not change the per-code quantity. Write $m_{\rm pc}$ for the entanglement version when no superscript appears.

Relevant declarations include `CriticalDepth.IndependentFaultHistories.Law`, `CriticalDepth.FaultHistoryExperimentNormalization.PaperExperiment`, `paperPerCodeExponent`, `CriticalDepth.FaultExponent.exponent`, `CriticalDepth.FaultCPTPOptimality.optimalInfidelity_eq_cptp_inf`, `CriticalDepth.FaultChannelEffects.paperCircuitDiamond_eq_halfCBTraceNorm` and `CriticalDepth.FaultChannelEffects.exists_cptp_optimalHistoryDiamond`.

<a id="s7"></a>
## S7. First uncorrectable order and two-history ambiguity

Fix a circuit and its finite history carrier. In coordinates where the intended logical action has been removed, let $A_x:\mathcal H_L\to\mathcal H$ be the encoded isometric branch for history $x$. Thus $A_x^\dagger A_x=I_L$. Define

```math
\operatorname{CorrectableThrough}(r)\iff
\forall x,y\ (f(x)\le r)\ (f(y)\le r),
\quad \exists c_{xy}\in\mathbb C,
\quad A_x^\dagger A_y=c_{xy}I_L.
```

Both histories separately have at most $r$ faults; the condition is not a bound of $r$ on their combined fault count. This joint Knill–Laflamme condition is equivalent to the existence of one CPTP recovery correcting every branch in that set exactly. It holds at $r=0$.

Let

```math
r_* =\min\{r\in\mathbb N:\neg\operatorname{CorrectableThrough}(r)\},
```

with value $\infty$ when there is no failure. For every positive law of S6:

- If $r_*=\infty$, there exists one terminal CPTP recovery correcting all histories. All three optimized errors vanish for every $p\in[0,1]$.
- If $r_*=r<\infty$, then $r\ge1$, all lower orders are jointly correctable, order $r$ fails, and

```math
\epsilon^{\rm opt}(p)=\Theta(p^r),\qquad
r_{\rm av}^{\rm opt}(p)=\Theta(p^r),\qquad
\delta^{\rm opt}(p)=\Theta(p^r)
\quad(p\to0^+).
```

In particular, the three circuit exponents equal $r_*$ and do not depend on which strictly positive conditional law was chosen. Their numerical error values and optimizing recoveries need not agree.

The pointwise ambiguity bound uses two distinct histories $x\ne y$ of nonnegative probabilities $a,b$. If

```math
A_y=zA_xP,\qquad |z|=1,\qquad P\in U(K),\qquad \operatorname{tr}P=0,
```

then every common terminal recovery has total entanglement infidelity at least $\min(a,b)$, and so does the optimum. A traceless logical Pauli is the manuscript's special case of $P$. For the independent laws of S6, this gives an exponent upper bound of $\max\{f(x),f(y)\}$ when such a pair is present.

The endpoints are `CriticalDepth.FaultFirstBadOrder.correctableThrough_iff_common_cptp_recovery`, `historyErrors_firstUncorrectableOrder`, `paperCircuitErrorExponents_eq_firstUncorrectableOrder`, and `CriticalDepth.FaultPointwiseAmbiguity.minWeight_le_optimalCPTPInfidelity_of_ambiguous_pair`.

<a id="s8"></a>
## S8. Universal fault envelopes and their onset depths

For integers $d\ge2$, $\rho\ge2$, $h\ge1$, define

```math
m_-(\rho,d,h)=\left\lceil\frac{d}{\rho^h+\rho}\right\rceil,
\qquad
m_+(\rho,d,h)=\left\lceil\frac{d}{2\rho^{\lceil h/2\rceil}}\right\rceil.
```

### Theorem 3: universal bounds

For every qubit stabilizer subspace code $\mathcal C$ of actual distance $d$,

```math
m_-(\rho,d,h)\le m_{\rm pc}^{e}(\mathcal C;\rho,h)
\le m_+(\rho,d,h)
\quad(e=\epsilon,r_{\rm av},\delta).
```

The lower bound applies to every admissible circuit. The upper bound asserts the existence of a circuit on that same code with exponent at most $m_+$; it does not put an upper bound on the exponent of every circuit. No uniform asymptotic error constant across circuits or code sizes is asserted. The code and circuit are held constant in each small-$p$ bound.

The Lean endpoint is `CriticalDepth.Manuscript20261114.sharpFaultSuppression_bounds_allMetrics`. S9 and S10 give the attainability assertions in the two parts of Theorem 3.

### Correlated local-stochastic guarantee

The lower recovery bound also holds for a possibly correlated distribution over the same Pauli-history carrier. For a given $p\in[0,1]$, assume nonnegative normalized weights $w_p(x)$ and

```math
\forall F\subseteq\mathrm{Loc},\qquad
\sum_{x:\,F\subseteq\operatorname{faults}(x)}w_p(x)\le p^{|F|}.
```

Independence and positive conditional weights are not required for this guarantee. For every exact circuit of depth at most $h$ on a subspace code detecting all operators below $d$, one common recovery corrects every history with fewer than $m_-(\rho,d,h)$ faults. Consequently

```math
\epsilon^{\rm opt}(p),\ \delta^{\rm opt}(p)
\le {N_{\rm loc}\choose m_-(\rho,d,h)}p^{m_-(\rho,d,h)}.
```

The average-infidelity bound follows with the factor $K/(K+1)$. This statement only needs detection below $d$, not stabilizer structure or a witness of actual distance. Its endpoint is `CriticalDepth.FaultChannelEffects.paper_localStochastic_recovery_bounds_at_depth`.

### Loss of a superlinear worst-case guarantee

For $d>2\rho$, set

```math
h_-=\lceil\log_\rho(d-\rho)\rceil,
\qquad
h_+=2\lceil\log_\rho(d/2)\rceil-1.
```

These are the first positive depths at which $m_-$ and $m_+$, respectively, equal one. For stabilizer codes of actual distance $d$,

```math
h_-\le h_+\le h_\infty=H(\rho,d),
\qquad h_\infty-h_+\in\{0,2\}.
```

Below $h_-$, every admissible circuit has exponent at least two. In $h_-\le h<h_+$, the universal lower envelope is one but the upper envelope exceeds one. The Shor construction attains the lower envelope at $h_-$. For every $h\ge h_+$, each code admits a circuit of depth at most $h$ with all three optimized errors of order $\Theta(p)$, by the universal bounds and S7. These are statements about optimized terminal recovery, not about an arbitrary chosen decoder.

At the lower-envelope onset, for integers $\rho\ge2$ and $d>2\rho$,

```math
\frac{\sqrt d}{2\rho}
\le m_+(\rho,d,h_-)
\le 2\sqrt d.
```

Consequently, for each fixed $\rho\ge2$,

```math
m_+(\rho,d,h_-)=\Theta_\rho(\sqrt d)
\qquad(d\to\infty\text{ through integers}).
```

This is an arithmetic statement about the envelope as the distance grows; its constants may depend on $\rho$. The endpoints are `CriticalDepth.FaultDepthArithmetic.upperEnvelope_lowerOnset_squareRootBounds` and `CriticalDepth.FaultDepthArithmetic.upperEnvelope_lowerOnset_isTheta`.

<a id="s9"></a>
## S9. Shor saturation of the lower envelope

For every integer triple $d\ge2$, $\rho\ge2$, $h\ge1$, let

```math
s=m_-(\rho,d,h),\qquad N=s(\rho^h+\rho).
```

There exists an explicit $[[Nd,1,d]]$ rectangular Shor stabilizer code and a native circuit on its original $Nd$ qubits with exactly $h$ layers and exact logical identity action, such that for every positive conditional Pauli law of S6,

```math
\epsilon^{\rm opt}(p),\ r_{\rm av}^{\rm opt}(p),\ \delta^{\rm opt}(p)
=\Theta(p^s).
```

The same code and gate list work for all these laws. The constants in the three $\Theta$ bounds may depend on the law. For this code,

```math
m_{\rm pc}^{\epsilon}=m_{\rm pc}^{r_{\rm av}}=m_{\rm pc}^{\delta}=s.
```

The construction uses $N$ rows and $d$ columns, with stabilizer generators $X_{ij}X_{i,j+1}$ and products of $Z$ on two adjacent complete rows. Its logical $Z$ can have weight $d$, whereas the full-column logical $X$ has weight $N\ge d$; the actual distance is $d$. The witnessing histories each contain exactly $s$ faulty native locations and their output errors differ by that nontrivial logical $X$. The boundary permutation gates in the construction have nonempty supports and count as actual noisy locations.

The quantifier order is

```math
\forall d,\rho,h\ \exists\mathcal C\ \exists L\ \forall a\text{ as in S6},
\quad\text{the stated distance, exact action, depth and three error orders hold}.
```

The endpoint is `CriticalDepth.Manuscript20261114.sharpFaultSuppression_lower_paper_witness_allMetrics`.

<a id="s10"></a>
## S10. CSS rigidity and saturation of the upper envelope

### Check-space hypotheses and whole-unitary rigidity

For a binary subspace $B\subseteq\mathbb F_2^n$, let $\operatorname{dist}(B)$ be its minimum nonzero Hamming weight, with $\operatorname{dist}(\{0\})=\infty$. Let $H,J\subseteq\mathbb F_2^n$ satisfy $J\subseteq H^\perp$. Set

```math
a=\dim H,\qquad b=\dim J,\qquad D=a+1,\qquad L=J^\perp.
```

The CSS code is the span of the orthonormal coset states

```math
|x+H\rangle=|H|^{-1/2}\sum_{y\in x+H}|y\rangle,
\qquad x+H\in L/H.
```

For integers $\rho\ge2$ and $t\ge1$, put $R=\rho^t$. Suppose $a\ge1$, $a+b<n$, and all four conditions hold:

1. $\operatorname{dist}(H^\perp)>R+1$ and $\operatorname{dist}(J^\perp)>RD$.
2. $\operatorname{dist}(J)>T$, where $T=\max\{RD,(b+1)(R+1)+R\}$.
3. If $F\in\operatorname{GL}(n,\mathbb F_2)$ has every row and column of weight at most $R$ and $FH=H$, then $F=I$.
4. If $Q$ is a symmetric binary matrix with every row of weight at most $R+1$ and $QH\subseteq J$, then $Q=0$.

Every exact code-preserving circuit on the original $n$ qubits, with depth at most $t$ and native gate arity at most $\rho$, then has total physical unitary equal, up to global phase, to a tensor product of single-qubit Paulis. This constrains the unitary on the entire physical Hilbert space, not only its action on the code. It does not assume that the constituent gates are Clifford or Pauli.

The conditions are represented by `CriticalDepth.Manuscript20261114.CSSCheckSpaces.RigidityCheckSpaces`. The physical conclusion is `CriticalDepth.Manuscript20261114.CSSCheckSpaces.physicalCSS_exactCircuit_tensorPauli`, using a check matrix whose existence is proved separately.

### Existence and simultaneous upper saturation

For each fixed $\rho\ge2$ and all sufficiently large integers $t$, there exist check spaces as above with

```math
R=\rho^t,\qquad n=R^{12},\qquad
a=R^4,\qquad b=R^6,\qquad
\operatorname{dist}(H^\perp)=d=R^2.
```

The formal construction supplies $t\ge20$ as a sufficient cutoff. A planted nonzero word of weight $R^2$ lies in $H^\perp\setminus J$ and supplies an actual-distance witness. The resulting physical CSS code has parameters

```math
[[R^{12},\ R^{12}-R^4-R^6,\ R^2]].
```

The same code $\mathcal C_t$ satisfies, for every integer $1\le h\le t$,

```math
m_{\rm pc}^{\epsilon}(\mathcal C_t;\rho,h)
=m_{\rm pc}^{r_{\rm av}}(\mathcal C_t;\rho,h)
=m_{\rm pc}^{\delta}(\mathcal C_t;\rho,h)
=m_+(\rho,R^2,h).
```

For each such $h$ there is an actual gate list of depth at most $h$ attaining this order simultaneously for the three separately optimized metrics, for every positive conditional law. The code is chosen before $h$, and the witnessing gate list is chosen before the law:

```math
\forall\rho\ge2\ \forall t\ge20\ \exists\mathcal C_t\quad
\forall h\in\{1,\ldots,t\}\ \exists L_h\ \forall a\text{ as in S6},
\quad e^{\rm opt}_{L_h,a}(p)=\Theta\bigl(p^{m_+(\rho,R^2,h)}\bigr)
\quad(e=\epsilon,r_{\rm av},\delta).
```

No whole-circuit Clifford restriction is imposed in taking the worst-case exponent. Rigidity is proved for all allowed exact native circuits, and it supplies the stronger correctability bound used on this family.

At $h=t$, with $d=\rho^{2t}$,

```math
m_+(\rho,d,t)>m_-(\rho,d,t),\qquad
m_+(\rho,d,t)=\Theta_\rho(d^{3/4}),\qquad
m_-(\rho,d,t)=\Theta(\sqrt d).
```

The formal estimates include

```math
\frac{d^{3/4}}{2\rho}\le m_+(\rho,d,t)\le2d^{3/4},
\qquad \frac{\sqrt d}{2}\le m_-(\rho,d,t)\le\sqrt d.
```

The rate is $1-R^{-8}-R^{-6}$ and tends to one. Both distance and the simultaneous depth interval grow with $t$. A finite exhaustive selection can enumerate row-reduced bases and the stated finite distance and matrix conditions; existence guarantees a successful pair for sufficiently large $t$. No efficient selection complexity or continuous-circuit search is claimed.

The endpoints include `CriticalDepth.Manuscript20261114.sharpFaultSuppression_upper_paper_witness_allMetrics`, `CriticalDepth.Manuscript20261114.CSSCheckSpaces.exists_rigid_checkSpaces`, `exists_css_code_with_strict_exponent_gap` and `exists_css_code_with_midpoint_scaling`. The manuscript's probabilistic estimates and the Lean finite sampling estimates establish the same existence conclusion by different intermediate arguments.

<a id="s11"></a>
## S11. Exact synthesis and the two threshold examples

### Selected Pauli directions give an exact generator bound

Let $\mathcal C$ be an $[[n,k,d]]$ qubit stabilizer subspace code with $k\ge1$, $d\ge2$, and let $\rho\ge2$. Choose a logical Pauli frame $\{\overline X_i,\overline Z_i\}_{i=1}^k$ and a connected tree $T$ on its $k$ logical qubits. The frame consists of Hermitian involutions: $\overline X_i$ and $\overline Z_i$ anticommute for the same index, and operators at different indices commute. Equivalently, a single unitary change of logical coordinates identifies them with the standard single-qubit $X_i,Z_i$. The statement ranges over frames equipped with the physical Pauli representatives specified below; the frame relations alone do not guarantee such representatives for an arbitrary abstract frame. For $k=1$ the edge set is empty. For each direction in

```math
\mathcal F_T=
\{\overline X_i,\overline Z_i:1\le i\le k\}
\cup\{\overline Z_i\overline Z_j:ij\in E(T)\},
```

choose a Hermitian physical Pauli representative $P_A$ inducing $A$ on the encoded space, and set $D=\max_{A\in\mathcal F_T}\operatorname{wt}(P_A)$. Each direction is nontrivial, so $d\le D\le n$. Edge representatives may be selected independently within their stabilizer cosets. Minimum-weight choices are allowed but not required for the bound.

```math
H(\rho,d)\le h_{\rm exact}(\mathcal C;\rho)
\le H(\rho,D)\le H(\rho,n).
```

For every $A\in\mathcal F_T$ and every real $t$, $e^{itA}$ has an exact physical implementation at depth at most $H(\rho,D)$. Finite words in these rotations generate all of $PU(2^k)$. Thus, after choosing the code, directions and representatives, every target logical unitary has a finite synthesis using those directions. If the expanded word has $r$ primitive rotations, its complete physical circuit has depth at most $rH(\rho,D)$. A global scalar, if retained instead of quotienting it out, can be restored on a physical gate; the zero-angle primitive used for an otherwise empty word is counted in $r$.

The construction permits exact real gate parameters and gives no efficient gate-count guarantee. The formal interfaces include `CriticalDepth.Manuscript20261114.exact_generator_depth_bounds_of_connectedPauliFrame` and `exists_stabilizer_native_exact_givens`; the latter selects minimum-weight representatives and supplies an exact native circuit on the original encoding for every target.

### Rectangular Bacon–Shor subsystem codes

Let $2\le m\le b$ and consider the $m\times b$ Bacon–Shor subsystem code whose gauge group is generated by horizontal adjacent $XX$ pairs and vertical adjacent $ZZ$ pairs. It has parameters $[[mb,1,(m-1)(b-1),m]]$: one protected logical qubit and $(m-1)(b-1)$ gauge qubits. Its dressed distance and its minimum nontrivial bare logical Pauli weight both equal $m$.

For every $\rho\ge2$,

```math
\begin{aligned}
h_\infty&=H(\rho,m),\\
\max\{h_\infty,\lceil\log_\rho(b/m)\rceil\}
&\le h_{\rm exact}\le H(\rho,b).
\end{aligned}
```

If $m\le b\le\rho^{\lceil\log_\rho m\rceil}$, then $h_{\rm exact}=h_\infty$. If $b>m\rho^{h_\infty}$, then

```math
h_\infty<h_{\rm dense}=h_{\rm exact}.
```

The obstruction uses the normalized gauge trace: when $m\rho^h<b$, every allowed logical generator preserves the short logical $X$ axis up to sign. Its generated group and closure therefore remain in a proper closed axis normalizer. The result concerns the subsystem implementation equation with an arbitrary gauge unitary, not an imposed identity gauge action for every circuit.

For fixed $\rho\ge2$, the nonsquare family $m=\rho^j+1$, $b=\rho^{j+1}$, $j\ge1$, has $h_{\rm exact}=h_\infty=2j+1$. The formal endpoint `CriticalDepth.FaultShorSaturation.BaconShor.baconShor_proposition` uses predecessor parameters: its arguments `m,b` represent a physical rectangle of size $(m+1)\times(b+1)$. The manuscript's $m\times b$ rectangle therefore uses Lean arguments $m-1,b-1$.

### The concrete 37-qubit CSS code

For the particular $[[37,1,7]]$ CSS code $Q_{37}$ specified in the manuscript and encoded by `q37CanonicalCode`, at arity $\rho=3$,

```math
h_{\rm dense}=1,\qquad h_\infty=h_{\rm exact}=3.
```

Its two specified depth-one projective classes contain representatives $D=\operatorname{diag}(1,e^{-i\pi/4})$ and $B=e^{i\pi X/4}$. Their finite words give $H=D^2BD^2$ and $T=D^7$, hence dense generation. A weight-seven bare $Z$ rotation has a three-layer implementation; together with the generated Hadamard it supplies two continuous axes and exact one-qubit synthesis. The final endpoint is `CriticalDepth.Q37BinaryData.q37CanonicalCode_thresholds`. This is a statement about the concrete checked code, not every code with parameters $[[37,1,7]]$.

### Evidence boundary

These statements retain exact error detection, exact code preservation and the specified stochastic Pauli model. They do not extend the results to approximate encodings, general coherent noise, noisy recovery circuits, unrestricted ancillas or a uniform error constant over growing systems. Correspondence with the final Lean propositions and actual replay acceptance are separate checks. Historical author approvals retain their recorded inputs and do not automatically approve this new specification.
