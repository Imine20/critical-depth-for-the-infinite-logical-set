# Pure mathematical statements

Let \(n\ge1\), \(K\ge2\), and \(g\ge1\) be integers. Let
\(\mathcal H=\bigotimes_{i=1}^n\mathcal H_i\), where each \(\mathcal H_i\)
is a finite-dimensional complex Hilbert space, and let
\[
 V:\mathbb C^K\otimes\mathbb C^g\longrightarrow\mathcal H,
 \qquad V^\dagger V=I_{Kg}.
\]
For a subset \(S\subseteq\{1,\ldots,n\}\), write
\(\operatorname{supp}(O)\subseteq S\) when \(O\) acts as the identity on
the complementary tensor factors. Define
\[
 \operatorname{DetectsBelow}(V,d)
 \iff
 \forall S,\ |S|<d\ \Longrightarrow\
 \forall O\in\operatorname{End}(\mathcal H),\
 \operatorname{supp}(O)\subseteq S\ \Longrightarrow\
 \exists M\in M_g(\mathbb C),\quad
 V^\dagger OV=I_K\otimes M.
\]
Define
\[
\begin{aligned}
 \operatorname{ActualDistance}(V,d)\iff{}&
 \operatorname{DetectsBelow}(V,d)\\
 &\land\ \exists S,\ |S|=d,\ \exists O\in\operatorname{End}(\mathcal H),\
 \operatorname{supp}(O)\subseteq S,\
 \forall M\in M_g(\mathbb C),\ V^\dagger OV\ne I_K\otimes M.
\end{aligned}
\]

For integers \(q,h\ge0\), let \(\mathcal U_{q,\le h}\) be the physical
unitaries implemented by circuits on these same \(n\) factors with
\(r\) layers for some \(0\le r\le h\). Each layer is an arbitrary finite
product of unitary gates on pairwise disjoint supports of cardinality at most
\(q\). Every unitary matrix on an allowed support is permitted.

Let \([W]\) identify only a single global phase,
\(W\sim W'\iff\exists z\in\mathbb C,\ |z|=1,\ W'=zW\), and equip
\(\mathrm{PU}(K)=\mathrm U(K)/\mathrm U(1)\) with its quotient topology.
Define
\[
 \mathcal L_{\le h}(V;q)=
 \left\{[W]\in\mathrm{PU}(K):
 \exists U\in\mathcal U_{q,\le h},\ \exists Z\in\mathrm U(g),\
 UV=V(W\otimes Z)\right\}.
\]
For \(q\ge2\), \(d\ge2\), put
\[
 H(q,d)=2\lceil\log_q d\rceil-1,
 \qquad
 h_\infty^+(V;q)=
 \min\{h\in\mathbb Z_{\ge1}:\mathcal L_{\le h}(V;q)\text{ is infinite}\},
\]
where the minimum of the empty set is \(\infty\).

**Theorem 1.** For every encoding \(V\) as above and all integers
\(d\ge2\), \(q\ge2\), \(h\ge1\),
\[
 \operatorname{DetectsBelow}(V,d)\ \land\ h<H(q,d)
 \quad\Longrightarrow\quad
 \mathcal L_{\le h}(V;q)\text{ is finite}
 \quad\land\quad
 \overline{\mathcal L_{\le h}(V;q)}\ne\mathrm{PU}(K).
\]

**Theorem 2.** Let \(k\ge1\), \(d\ge2\), and \(q\ge2\) be integers, and
let \(V:\mathbb C^{2^k}\to(\mathbb C^2)^{\otimes n}\) be an isometry
with \(\operatorname{ActualDistance}(V,d)\), taking \(g=1\). Suppose that
there is a subgroup \(G\) of the \(n\)-qubit Pauli group such that
\[
 \operatorname{ran}V=
 \{\psi\in(\mathbb C^2)^{\otimes n}:\ \forall P\in G,\ P\psi=\psi\}.
\]
Then
\[
 h_\infty^+(V;q)=H(q,d).
\]
Moreover, there exists a continuous map
\(F:\mathbb R\to\mathrm U(2^k)\) satisfying
\[
 F(0)=I,\qquad
 \forall s,t\in\mathbb R,\quad F(s+t)=F(s)F(t),
\]
\[
 \exists t\in\mathbb R,\quad [F(t)]\ne[I],
 \qquad
 \forall t\in\mathbb R,\quad
 [F(t)]\in\mathcal L_{\le H(q,d)}(V;q).
\]
