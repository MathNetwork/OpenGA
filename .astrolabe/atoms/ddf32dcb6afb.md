---
chapter: '3'
dcref: ch3:3.6
ref:
- ddf32dcb6afb
sort: proposition
source: tex
src: docarmo
title: geodesics locally minimize
---
Let $p\in M$, $U$ a normal neighborhood of $p$, and $B\subset U$ a normal ball of
center $p$. Let $\gamma:[0,1]\to B$ be a geodesic segment with $\gamma(0)=p$. If
$c:[0,1]\to M$ is any piecewise differentiable curve joining $\gamma(0)$ to
$\gamma(1)$, then $\ell(\gamma)\le\ell(c)$, and if equality holds then
$\gamma([0,1])=c([0,1])$.
*Proof.* Suppose first $c([0,1])\subset B$. For $t\ne 0$ write uniquely
$c(t)=\exp_p(r(t)\,v(t))=f(r(t),t)$, $|v(t)|=1$, $r:(0,1]\to\mathbb{R}$ positive
piecewise differentiable. Then except at finitely many points
$\frac{dc}{dt}=\frac{\partial f}{\partial r}r'(t)+\frac{\partial f}{\partial t}$.
By the Gauss lemma $\langle\frac{\partial f}{\partial r},\frac{\partial f}{\partial t}\rangle=0$
and $|\frac{\partial f}{\partial r}|=1$, so

$$
\Big|\frac{dc}{dt}\Big|^2=|r'(t)|^2+\Big|\frac{\partial f}{\partial t}\Big|^2\ge|r'(t)|^2,\qquad\text{(1)}
$$

$$
\int_\varepsilon^1\Big|\frac{dc}{dt}\Big|dt\ge\int_\varepsilon^1|r'(t)|dt\ge r(1)-r(\varepsilon).\qquad\text{(2)}
$$

Letting $\varepsilon\to0$ gives $\ell(c)\ge r(1)=\ell(\gamma)$. If equality holds
then $|\frac{\partial f}{\partial t}|=0$ and $r'(t)>0$, so $c$ is a monotone
reparametrization of $\gamma$ and $c([0,1])=\gamma([0,1])$. If $c([0,1])\not\subset B$,
let $t_1$ be the first time $c(t_1)\in\partial B$; with $\rho$ the radius of $B$,
$\ell(c)\ge\ell_{[0,t_1]}(c)\ge\rho>\ell(\gamma)$. $\square$

The proposition is not global: a sufficiently long geodesic arc can cease to
minimize (e.g. geodesics on the sphere past the antipode of $p$).