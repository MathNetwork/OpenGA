---
chapter: '12'
dcref: ch12:2.2
ref:
- ddfcde2073b7
sort: theorem
source: tex
src: docarmo
title: Cartan
---
If $M$ is compact and $\mathcal{L}\in C_1(M)$ is not the constant class, then
there exists a closed geodesic of $M$ in the class $\mathcal{L}$.

*Proof.* Let $d$ be the infimum of the lengths of piecewise differentiable curves
belonging to $\mathcal{L}$. Since $\mathcal{L}$ is not trivial, $d>0$. Let
$\gamma_j$ be a sequence of piecewise differentiable curves belonging to
$\mathcal{L}$ such that $\ell(\gamma_j)\to d$. We can suppose that $\gamma_j$ is a
broken geodesic defined on $[0,1]$ parametrized proportionally to arc length. Let
$L=\sup\ell(\gamma_j)$. Then

$$
d(\gamma_j(t_1),\gamma_j(t_2))\leq\int_{t_1}^{t_2}|\gamma_j'(t)|\,dt\leq L(t_2-t_1),
$$

for all $t_1\leq t_2\in[0,1]$. Therefore the set $\{\gamma_j\}$ is equicontinuous.
Since $M$ is compact, there exists a subsequence of $\gamma_j$, which we denote
again by $\gamma_j$, which converges uniformly to a continuous closed curve
$\gamma_o:[0,1]\to M$.

Now let $0=t_o<t_1<\cdots<t_k=1$ be a partition of $[0,1]$ such that
$\gamma_o|_{[t_{i-1},t_i]}$, $i=1,\dots,k$, is contained in a totally normal
neighborhood. Let $\gamma:[0,1]\to M$ be a piecewise differentiable curve such
that $\gamma^i=\gamma|_{[t_{i-1},t_i]}$ is the unique geodesic segment which joins
the points $\gamma_o(t_{i-1})$ and $\gamma_o(t_i)$. It is clear that
$\gamma\in\mathcal{L}$, hence $\ell(\gamma)\geq d$. We show that $\ell(\gamma)=d$.

Suppose that $\ell(\gamma)>d$ and let $\varepsilon=\frac{\ell(\gamma)-d}{2k+1}$.
There exists an integer $j$ such that

$$
\ell(\gamma_j)-d<\varepsilon\quad\text{and}\quad d(\gamma_j(t),\gamma_o(t))<\varepsilon,\ \text{for all }t\in[0,1].
$$

Denoting by $\gamma_j^i=\gamma_j|_{[t_{i-1},t_i]}$, we have

$$
\sum_{i=1}^k(\ell(\gamma_j^i)+2\varepsilon)=\ell(\gamma_j)+2k\varepsilon<d+(2k+1)\varepsilon=\ell(\gamma)=\sum_{i=1}^k\ell(\gamma^i).
$$

Therefore, there exists an integer $i$, $1\leq i\leq k$, such that
$\ell(\gamma_j^i)+2\varepsilon<\ell(\gamma^i)$, which contradicts the fact that
$\gamma^i$ is minimizing and proves that $\ell(\gamma)=d$.

We parametrize $\gamma$ by arc length. Then $\gamma:[0,d]\to M$ is a broken
geodesic which has minimum length in the class $\mathcal{L}$. We show that
$\gamma$ is regular at the point $p_i=\gamma(t_i)$, for all $i=0,\dots,k$. Suppose
to the contrary and let $B$ be a convex ball centered at $p_i$. Choose points
$q_1$ and $q_2$ in $\gamma\cap B$ in a way that the geodesic triangle
$p_iq_1q_2$ is homotopic to a point. Then the closed curve constituted by the
minimizing geodesic $q_1q_2$ and by the arc of $\gamma$ between $q_1$ and $q_2$
that does not contain $p_i$ is in the class $\mathcal{L}$ and has length smaller
than $\gamma$, which is a contradiction. $\blacksquare$