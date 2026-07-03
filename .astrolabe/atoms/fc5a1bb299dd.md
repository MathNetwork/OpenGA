---
chapter: '0'
dcref: ch0:5.5
ref:
- fc5a1bb299dd
sort: lemma
source: tex
src: docarmo
title: Hadamard-type lemma from calculus
---
Let $h:(-\delta,\delta)\times U\to\mathbb{R}$ be differentiable with $h(0,q)=0$
for all $q\in U$. Then there exists a differentiable
$g:(-\delta,\delta)\times U\to\mathbb{R}$ with $h(t,q)=t\,g(t,q)$; in particular
$g(0,q)=\frac{\partial h(t,q)}{\partial t}\big|_{t=0}$.
*Proof.* Define $g(t,q)=\int_0^1\frac{\partial h(ts,q)}{\partial(ts)}\,ds$; after
changing variables, $t\,g(t,q)=\int_0^t\frac{\partial h(ts,q)}{\partial(ts)}\,d(ts)=h(t,q)$.
$\square$

*Topology of manifolds.* Up to here no restriction was put on the topology. Two
axioms may fail: **A) Hausdorff Axiom** — distinct points have disjoint
neighborhoods; **B) Countable Basis Axiom** — $M$ is covered by countably many
coordinate neighborhoods. Axiom A is essential for uniqueness of limits, Axiom B
for the existence of a differentiable partition of unity. (If $M$ is connected,
A and B together are equivalent to the existence of a partition of unity; see
\entryref{b89377b6ed34}.) A fundamental embedding result is *Whitney's theorem*: any
differentiable manifold (Hausdorff, countable basis) of dimension $n$ can be
immersed in $\mathbb{R}^{2n}$ and embedded in $\mathbb{R}^{2n+1}$ (refinable to
$\mathbb{R}^{2n-1}$, $n>1$, and $\mathbb{R}^{2n}$ respectively); proof in Hirsch
[Hi].

A family of open sets $V_\alpha\subset M$ with $\bigcup_\alpha V_\alpha=M$ is
*locally finite* if every $p\in M$ has a neighborhood $W$ with $W\cap V_\alpha\neq\phi$
for only finitely many indices. The *support* of $f:M\to\mathbb{R}$ is the
closure of $\{f\neq0\}$. A family $\{f_\alpha\}$ of differentiable
$f_\alpha:M\to\mathbb{R}$ is a *differentiable partition of unity* if:
(1) $f_\alpha\ge0$ and $\mathrm{supp}\,f_\alpha\subset$ a coordinate neighborhood
$V_\alpha=\mathbf{x}_\alpha(U_\alpha)$ of a differentiable structure;
(2) $\{V_\alpha\}$ is locally finite;
(3) $\sum_\alpha f_\alpha(p)=1$ for all $p\in M$.
The partition is *subordinate to the covering* $\{V_\alpha\}$.