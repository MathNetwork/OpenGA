---
chapter: '0'
dcref: ch0:4.7
ref:
- 6afdbc4ac929
sort: example
source: tex
src: docarmo
title: another description of projective space
---
$P^n(\mathbb{R})$ is the quotient of the unit sphere $S^n=\{p\in\mathbb{R}^{n+1};
|p|=1\}$ by $p\sim A(p)=-p$. Introducing on $S^n\subset\mathbb{R}^{n+1}$ the
regular-surface structure with hemisphere parametrizations
$\mathbf{x}_i^{\pm}:U_i\to S^n$,
$U_i=\{x_i=0,\,x_1^2+\dots+x_{i-1}^2+x_{i+1}^2+\dots+x_{n+1}^2<1\}$,
$\mathbf{x}_i^{\pm}(x_1,\dots,\hat x_i,\dots,x_{n+1})=(x_1,\dots,\pm D_i,\dots,x_{n+1})$,
$D_i=\sqrt{1-(x_1^2+\dots+x_{i-1}^2+x_{i+1}^2+\dots+x_{n+1}^2)}$. With the
canonical projection $\pi:S^n\to P^n(\mathbb{R})$, $\pi(p)=\{p,-p\}$, define
$\mathbf{y}_i=\pi\circ\mathbf{x}_i^+:U_i\to P^n(\mathbb{R})$. Then
$\mathbf{y}_i^{-1}\circ\mathbf{y}_j=(\mathbf{x}_i^+)^{-1}\circ\mathbf{x}_j^+$ is
differentiable, so $\{(U_i,\mathbf{y}_i)\}$ is a differentiable structure for
$P^n(\mathbb{R})$, giving the same maximal structure as \entryref{db3f06f618e5}. As shown in
Exercise 9, $P^n(\mathbb{R})$ is orientable if and only if $n$ is odd.