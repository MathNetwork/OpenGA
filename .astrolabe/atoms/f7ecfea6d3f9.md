---
chapter: '0'
dcref: ch0:2.5
ref:
- f7ecfea6d3f9
sort: definition
source: tex
src: docarmo
title: differentiable mapping
---
Let $M_1^n$ and $M_2^m$ be differentiable manifolds. A mapping
$\varphi:M_1\to M_2$ is *differentiable at* $p\in M_1$ if, given a parametrization
$\mathbf{y}:V\subset\mathbb{R}^m\to M_2$ at $\varphi(p)$, there is a
parametrization $\mathbf{x}:U\subset\mathbb{R}^n\to M_1$ at $p$ with
$\varphi(\mathbf{x}(U))\subset\mathbf{y}(V)$ such that

$$
\mathbf{y}^{-1}\circ\varphi\circ\mathbf{x}:U\subset\mathbb{R}^n\to\mathbb{R}^m\qquad\text{(1)}
$$

is differentiable at $\mathbf{x}^{-1}(p)$. By condition (2) of \entryref{e393a9b2a18c}
this is independent of the choice of parametrizations. The mapping (1) is the
*expression* of $\varphi$ in the parametrizations $\mathbf{x}$ and $\mathbf{y}$.