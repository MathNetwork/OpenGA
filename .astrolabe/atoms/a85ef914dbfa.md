---
chapter: '5'
dcref: ch5:2.7
ref:
- a85ef914dbfa
sort: proposition
source: tex
src: docarmo
title: Proposition 2.7
---
Let $p\in M$ and $\gamma:[0,a]\to M$ be a geodesic with $\gamma(0)=p$,
$\gamma'(0)=v$. Let $w\in T_v(T_p M)$ with $|w|=1$ and let $J$ be a Jacobi field
along $\gamma$ given by

$$
J(t)=(d\exp_p)_{tv}(tw),\quad 0\le t\le a.
$$

Then the Taylor expansion of $|J(t)|^2$ about $t=0$ is given by

$$
|J(t)|^2=t^2-\tfrac{1}{3}\langle R(v,w)v,w\rangle t^4+R(t),\qquad(3)
$$

where $\lim_{t\to 0}\frac{R(t)}{t^4}=0$.

*Proof.* Since $J(0)=0$ and $J'(0)=w$, the first three coefficients are

$$
\langle J,J\rangle(0)=0,\quad\langle J,J\rangle'(0)=2\langle J,J'\rangle(0)=0,\quad\langle J,J\rangle''(0)=2\langle J',J'\rangle(0)+2\langle J'',J\rangle(0)=2.
$$

Since $J''(0)=-R(\gamma',J)\gamma'(0)=0$, we have
$\langle J,J\rangle'''(0)=6\langle J',J''\rangle(0)+2\langle J''',J\rangle(0)=0$. Now
we need the fact

$$
\nabla_{\gamma'}(R(\gamma',J)\gamma')(0)=R(\gamma',J')\gamma'(0).\qquad(4)
$$

To prove (4), note that for any $W$, at $t=0$,

$$
\Big\langle\frac{D}{dt}(R(\gamma',J)\gamma'),W\Big\rangle
=\frac{d}{dt}\langle R(\gamma',W)\gamma',J\rangle-\langle R(\gamma',J)\gamma',W'\rangle
=\Big\langle\frac{D}{dt}(R(\gamma',W)\gamma'),J\Big\rangle+\langle R(\gamma',W)\gamma',J'\rangle
=\langle R(\gamma',J')\gamma',W\rangle,
$$

which implies (4). It follows from (4) and the Jacobi equation that
$J'''(0)=-R(\gamma',J')\gamma'(0)$. Therefore,

$$
\langle J,J\rangle''''(0)=8\langle J',J'''\rangle(0)+6\langle J'',J''\rangle(0)+2\langle J'''',J\rangle(0)=-8\langle J',R(\gamma',J')\gamma'\rangle(0)=-8\langle R(v,w)v,w\rangle.
$$

Putting together the calculation above, we obtain (3). $\square$