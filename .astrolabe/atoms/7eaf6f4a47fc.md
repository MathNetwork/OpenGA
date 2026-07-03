---
chapter: '0'
dcref: ch0:4.6
ref:
- 7eaf6f4a47fc
sort: example
source: tex
src: docarmo
title: the sphere $S^n$ is orientable
---
$S^n=\{(x_1,\dots,x_{n+1})\in\mathbb{R}^{n+1};\sum_{i=1}^{n+1}x_i^2=1\}$. With
north/south poles $N=(0,\dots,0,1)$, $S=(0,\dots,0,-1)$, the *stereographic
projections* $\pi_1:S^n-\{N\}\to\mathbb{R}^n$,
$\pi_1(x)=\big(\frac{x_1}{1-x_{n+1}},\dots,\frac{x_n}{1-x_{n+1}}\big)$, and
$\pi_2:S^n-\{S\}\to\mathbb{R}^n$ (from the south pole) are differentiable
injections onto $x_{n+1}=0$. The parametrizations
$(\mathbb{R}^n,\pi_1^{-1}),(\mathbb{R}^n,\pi_2^{-1})$ cover $S^n$ with change of
coordinates $y_j'=\frac{y_j}{\sum_{i=1}^n y_i^2}$, differentiable. For $n\geq2$,
$\pi_1^{-1}(\mathbb{R}^n)\cap\pi_2^{-1}(\mathbb{R}^n)=S^n-\{N,S\}$ is connected,
so by \entryref{6bc07ca778f4}, $S^n$ is orientable. For $n=1$, the same atlas is
orientable directly: on the two components of $S^1-\{N,S\}$, the change of
coordinates is $y'=1/y$ with derivative $-1/y^2<0$, and changing the sign of one
coordinate makes both transition derivatives positive. The antipodal map
$A:S^n\to S^n$, $A(p)=-p$, is a diffeomorphism ($A^2=\mathrm{id}$); it reverses the
orientation of $S^n$ when $n$ is even and preserves it when $n$ is odd.
