---
chapter: '10'
dcref: ch10:2.2
ref:
- 7a9c6afeabeb
sort: lemma
source: tex
src: docarmo
title: The Index Lemma
---
Let $\gamma:[0,a]\to M$ be a geodesic without conjugate points to $\gamma(0)$ in
the interval $(0,a]$. Let $J$ be a Jacobi field along $\gamma$, with
$\langle J,\gamma'\rangle=0$, and let $V$ be a piecewise differentiable vector
field along $\gamma$, with $\langle V,\gamma'\rangle=0$. Suppose that
$J(0)=V(0)=0$ and that $J(t_o)=V(t_o)$, $t_o\in(0,a]$. Then

$$
I_{t_o}(J,J)\leq I_{t_o}(V,V),
$$

and equality occurs if and only if $V=J$ on $[0,t_o]$.

*Proof.* The vector space $\mathcal{J}$ of Jacobi fields $J$ along $\gamma$ with
$J(0)=0$ and $\langle J,\gamma'\rangle=0$ has dimension $n-1$, where $n=\dim M$.
Let $\{J_1,\dots,J_{n-1}\}$ be a basis for this space; then $J=\sum_i\alpha_i J_i$
with constants $\alpha_i$. Since there are no conjugate points in $(0,a]$, for
all $t\neq 0$ the vectors $J_1(t),\dots,J_{n-1}(t)$ form a basis of the
orthogonal complement of $\gamma'(t)$, so for $t\neq 0$ we can write
$V(t)=\sum_i f_i(t)J_i(t)$, with $f_i$ piecewise differentiable on $(0,a]$. Using
\entryref{52ec647ed073} (write $J_i(t)=tA_i(t)$, so the $A_i(0)=J_i'(0)$ are linearly
independent, and $V(t)=\sum_i g_i(t)A_i(t)$ with $g_i(0)=0$, then $g_i(t)=th_i(t)$
with $f_i=h_i$), the $f_i$ extend piecewise differentiably to $[0,a]$.

One shows that, on the interior of each subinterval where $f_i$ is
differentiable,

$$
\langle V',V'\rangle-\langle R(\gamma',V)\gamma',V\rangle=\Big\langle\sum_i f_i'J_i,\sum_j f_j'J_j\Big\rangle+\frac{d}{dt}\Big\langle\sum_i f_iJ_i,\sum_j f_jJ_j'\Big\rangle.\qquad(1)
$$

Here one uses $R(\gamma',V)\gamma'=-\sum_i f_iJ_i''$, and the identity

$$
\Big\langle\sum_i f_iJ_i',\sum_j f_j'J_j\Big\rangle=\Big\langle\sum_i f_iJ_i,\sum_j f_j'J_j'\Big\rangle,\qquad(2)
$$

which follows from $h(t)=\langle J_i',J_j\rangle-\langle J_i,J_j'\rangle$ having
$h(0)=0$ and $h'(t)=-\langle R(\gamma',J_i)\gamma',J_j\rangle+\langle J_i,R(\gamma',J_j)\gamma'\rangle=0$,
so $h\equiv 0$. Applying (1) to $V$ and $J$,

$$
I_{t_o}(V,V)=\Big\langle\sum_i f_iJ_i,\sum_j f_jJ_j'\Big\rangle(t_o)+\int_0^{t_o}\Big\langle\sum_i f_i'J_i,\sum_j f_j'J_j\Big\rangle dt,
$$

$$
I_{t_o}(J,J)=\Big\langle\sum_i\alpha_iJ_i,\sum_j\alpha_jJ_j'\Big\rangle(t_o).
$$

Because $J(t_o)=V(t_o)$, we have $\alpha_i=f_i(t_o)$, hence

$$
I_{t_o}(V,V)=I_{t_o}(J,J)+\int_0^{t_o}\Big|\sum_i f_i'J_i\Big|^2 dt.\qquad(3)
$$

It follows from (3) that $I_{t_o}(V,V)\geq I_{t_o}(J,J)$. If equality holds, then
$\sum_i f_i'J_i=0$; since the $J_i$ are linearly independent for $t\neq 0$, by
continuity $f_i'=0$ for all $i$ on $[0,t_o]$. Therefore $f_i$ is constant, and
since $f_i(t_o)=\alpha_i$, we have $f_i(t)=\alpha_i$, that is, $V=J$. $\blacksquare$

We are now in a position to prove Rauch's Theorem. In what follows $M^n$ denotes
a manifold of dimension $n$.