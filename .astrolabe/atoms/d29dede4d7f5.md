---
chapter: '2'
dcref: ch2:2.2
ref:
- d29dede4d7f5
sort: proposition
source: tex
src: docarmo
title: covariant derivative along a curve
---
Let $M$ be a differentiable manifold with an affine connection $\nabla$. There
exists a unique correspondence which associates to a vector field $V$ along the
differentiable curve $c:I\to M$ another vector field $\frac{DV}{dt}$ along $c$,
called the *covariant derivative* of $V$ along $c$, such that:
- a) $\frac{D}{dt}(V+W)=\frac{DV}{dt}+\frac{DW}{dt}$.
- b) $\frac{D}{dt}(fV)=\frac{df}{dt}V+f\frac{DV}{dt}$, where $W$ is a vector field along $c$ and $f$ a differentiable function on $I$.
- c) If $V$ is induced by a vector field $Y\in\mathcal{X}(M)$, i.e. $V(t)=Y(c(t))$, then $\frac{DV}{dt}=\nabla_{dc/dt}Y$.

*Proof.* Suppose first a correspondence satisfying (a), (b), (c) exists. In a
coordinate system $\mathbf{x}:U\subset\mathbb{R}^n\to M$ write $V=\sum_j v^j X_j$
with $X_j=\frac{\partial}{\partial x_j}(c(t))$. By a) and b),
$\frac{DV}{dt}=\sum_j \frac{dv^j}{dt}X_j+\sum_j v^j\frac{DX_j}{dt}$. By c) and (i)
of \entryref{9ed91e02648c}, $\frac{DX_j}{dt}=\nabla_{dc/dt}X_j=\sum_i\frac{dx_i}{dt}\nabla_{X_i}X_j$.
Therefore

$$
\frac{DV}{dt}=\sum_j\frac{dv^j}{dt}X_j+\sum_{i,j}\frac{dx_i}{dt}v^j\nabla_{X_i}X_j.\qquad(1)
$$

Expression (1) shows uniqueness. For existence, define $\frac{DV}{dt}$ in
$\mathbf{x}(U)$ by (1); it has the desired properties, and on overlaps the local
definitions agree by uniqueness, so the definition extends over all of $M$.
$\blacksquare$