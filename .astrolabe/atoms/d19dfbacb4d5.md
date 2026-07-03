---
chapter: '9'
dcref: ch9:2.2
ref:
- d19dfbacb4d5
sort: proposition
source: tex
src: docarmo
title: existence of a variation with given variational field
---
Given a piecewise differentiable field $V(t)$, along the piecewise differentiable
curve $c:[0,a]\to M$, there exists a variation $f:(-\varepsilon,\varepsilon)\times[0,a]\to M$
of $c$, such that $V(t)$ is the variational field of $f$; in addition, if
$V(0)=V(a)=0$, it is possible to choose $f$ as a proper variation.

*Proof.* Since $c([0,a])\subset M$ is compact it is possible to find a $\delta>0$
such that $\exp_{c(t)}$ is well-defined for all $v\in T_{c(t)}M$ with $|v|<\delta$:
for each $c(t)$ consider a totally normal neighborhood $W_t$ of $c(t)$ and the
number $\delta_t>0$ associated to it (Theor. 3.7, Chap. 3); a finite subcover
$W_1,\dots,W_n$ of $c([0,a])$ gives $\delta=\min(\delta_1,\dots,\delta_n)$.
Consider $N=\max_{t\in[0,a]}|V(t)|$, $\varepsilon<\frac{\delta}{N}$ and define
$f(s,t)=\exp_{c(t)}sV(t)$. Since $\exp_{c(t)}sV(t)=\gamma(1,c(t),sV(t))$ and the
geodesic depends differentiably on the initial conditions, $f$ is piecewise
differentiable, and $f(0,t)=c(t)$. The variational field of $f$ is

$$
\frac{\partial f}{\partial s}(0,t)=\frac{d}{ds}(\exp_{c(t)}sV(t))\Big|_{s=0}=(d\exp_{c(t)})_0 V(t)=V(t),
$$

and if $V(0)=V(a)=0$ then $f$ is proper. $\square$

To compare the arc length of $c$ with that of neighboring curves we define
$L:(-\varepsilon,\varepsilon)\to\mathbf{R}$ by

$$
L(s)=\int_0^a\Big|\frac{\partial f}{\partial t}(s,t)\Big|\,dt,
$$

the length of the curve $f_s(t)$. It is more convenient to work with the *energy
function* $E(s)$ given by

$$
E(s)=\int_0^a\Big|\frac{\partial f}{\partial t}(s,t)\Big|^2\,dt,\qquad s\in(-\varepsilon,\varepsilon).
$$

For a curve $c:[0,a]\to M$ set

$$
L(c)=\int_0^a\Big|\frac{dc}{dt}\Big|\,dt,\qquad E(c)=\int_0^a\Big|\frac{dc}{dt}\Big|^2\,dt.
$$

Putting $f\equiv 1$ and $g=|\frac{dc}{dt}|$ in the Schwarz inequality
$(\int_0^a fg\,dt)^2\le\int_0^a f^2\,dt\cdot\int_0^a g^2\,dt$, we obtain

$$
L(c)^2\le a\,E(c),
$$

with equality if and only if $g$ is constant, that is, if and only if $t$ is
proportional to arc length.