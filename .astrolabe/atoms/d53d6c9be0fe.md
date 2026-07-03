---
chapter: '2'
dcref: ch2:2.3
ref:
- d53d6c9be0fe
sort: remark
source: tex
src: docarmo
title: Remark 2.3
---
The last line of (c) makes sense, since $\nabla_X Y(p)$ depends on the value of
$X(p)$ and the value of $Y$ along a curve tangent to $X$ at $p$. Part (iii) of
\entryref{9ed91e02648c} shows that the affine connection is a *local* notion (cf. \entryref{b75394389199}). In coordinates $(x_1,\dots,x_n)$ about $p$ with
$X=\sum_i x_i X_i$, $Y=\sum_j y_j X_j$, $X_i=\frac{\partial}{\partial x_i}$,

$$
\nabla_X Y=\sum_{ij}x_i y_j\nabla_{X_i}X_j+\sum_{ij}x_i X_i(y_j)X_j.
$$

Setting $\nabla_{X_i}X_j=\sum_k\Gamma_{ij}^k X_k$ with $\Gamma_{ij}^k$
differentiable,

$$
\nabla_X Y=\sum_k\Big(\sum_{ij}x_i y_j\Gamma_{ij}^k+X(y_k)\Big)X_k,
$$

which shows $\nabla_X Y(p)$ depends on $x_i(p)$, $y_k(p)$ and the derivatives
$X(y_k)(p)$.