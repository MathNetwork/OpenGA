---
chapter: '10'
dcref: ch10:4.8
ref:
- cdfac76c48af
sort: lemma
source: tex
src: docarmo
title: Index Lemma for focal points
---
Let $\gamma:[0,a]\to M^n$ be a geodesic which is focal point free on $(0,a]$. Let
$J$ be a Jacobi field along $\gamma$, with $\langle J,\gamma'\rangle=0$, and let
$V$ be a piecewise differentiable vector field along $\gamma$. Suppose that
$J'(0)=0$ and $J(t_o)=V(t_o)$, $t_o\in(0,a]$. Then

$$
I_{t_o}(J,J)\leq I_{t_o}(V,V),
$$

and the equality occurs if and only if $V=J$ on $[0,t_o]$.

*Proof.* Let $\{J_1,\dots,J_{n-1}\}$ be a basis of the vector space of Jacobi
fields $J$ such that $J'(0)=0$, $\langle J,\gamma'\rangle=0$. The fact that
$\gamma$ is focal point free on $(0,a]$ implies that, for each $t\in(0,a]$,
$\{J_1(t),\dots,J_{n-1}(t)\}$ is a basis for $(\gamma'(t))^\perp$. Starting from
there, the proof follows in a manner entirely analogous to the Index Lemma. $\blacksquare$