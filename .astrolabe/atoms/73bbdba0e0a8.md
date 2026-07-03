---
chapter: '6'
dcref: ch6:2.1
ref:
- 73bbdba0e0a8
sort: proposition
source: tex
src: docarmo
title: the second fundamental form mapping $B$
---
If $X,Y\in\mathcal{X}(U)$, the mapping
$B:\mathcal{X}(U)\times\mathcal{X}(U)\to\mathcal{X}(U)^\perp$ given by

$$
B(X,Y)=\overline{\nabla}_{\overline{X}}\overline{Y}-\nabla_X Y
$$

is bilinear and symmetric.

*Proof.* From linearity of a connection, $B$ is additive in $X$ and $Y$ and
$B(fX,Y)=fB(X,Y)$, $f\in\mathcal{D}(U)$. To show $B(X,fY)=fB(X,Y)$, denote the
extension of $f$ to $\overline{U}$ by $\overline{f}$; then

$$
B(X,fY)=\overline{\nabla}_{\overline{X}}(\overline{f}\,\overline{Y})-\nabla_X(fY)=\overline{f}\,\overline{\nabla}_{\overline{X}}\overline{Y}-f\nabla_X Y+\overline{X}(\overline{f})\overline{Y}-X(f)Y.
$$

Since $f=\overline{f}$, $\overline{X}(\overline{f})=X(f)$, and $Y=\overline{Y}$ on
$M$, the last two terms cancel, giving $B(X,fY)=fB(X,Y)$. To show $B$ is
symmetric, by symmetry of the Riemannian connection,

$$
B(X,Y)=\overline{\nabla}_{\overline{X}}\overline{Y}-\nabla_X Y=\overline{\nabla}_{\overline{Y}}\overline{X}+[\overline{X},\overline{Y}]-\nabla_Y X-[X,Y].
$$

Since $[\overline{X},\overline{Y}]=[X,Y]$ on $M$, we conclude $B(X,Y)=B(Y,X)$.
$\square$

Because $B$ is bilinear, the value $B(X,Y)(p)$ depends only on the values $X(p)$
and $Y(p)$. Now let $p\in M$ and $\eta\in(T_pM)^\perp$. The mapping
$H_\eta:T_pM\times T_pM\to\mathbb{R}$ given by

$$
H_\eta(x,y)=\langle B(x,y),\eta\rangle,\quad x,y\in T_pM,
$$

is, by Proposition 2.1, a symmetric bilinear form.