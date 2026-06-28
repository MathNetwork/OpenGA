---
chapter: 2
generator: tools/poincare_tex_extract.py
label: epsneck
labels:
- epsneck
mtref: '2.18'
ref:
- d91d54ddbd1c
sort: definition
source: tex
src: morgan-tian
tex_file: prelim
---
Let $(N,g)$ be a Riemannian manifold and $x\in N$ a point. Then *an $\epsilon$-neck structure on $(N,g)$
centered at $x$* consists of a diffeomorphism

$$
\varphi\colon  S^2\times (-\epsilon^{-1},\epsilon^{-1})\to N,
$$

with $x\in \varphi(S^2\times\{0\})$, such that the metric
$R(x)\varphi^*g$ is within $\epsilon$ in the
$C^{[1/\epsilon]}$-topology of the product of the usual Euclidean
metric on the open interval with the metric of constant Gaussian
curvature $1/2$ on $S^2$. We also use the terminology *$N$ is an
$\epsilon$-neck centered at $x$*. The image under $\varphi$ of the
family of submanifolds $S^2\times \{t\}$ is called the *family
of $2$-spheres of the $\epsilon$-neck*. The submanifold
$\varphi(S^2\times \{0\})$ is called *the central $2$-sphere* of
the $\epsilon$-neck structure. We denote by $s_N\colon N\to \Ar$
the composition $p_2\circ \varphi^{-1}$, where $p_2$ is the
projection of $S^2\times (-\epsilon^{-1},\epsilon^{-1})$ to the
second factor. There is also the vector field $\partial/\partial
s_N$ on $N$ which is $\varphi_*$ of the standard vector field in the
interval-direction of the product. We also use the terminology of
the *plus* and *minus* end of the $\epsilon$-neck in the
obvious sense. The opposite (or reversed) $\epsilon$-neck structure
is the one obtained by composing the structure map with $\mathit{Id}_{S^2}\times -1$. We define the
 *positive half of the neck* to be the region
$s_N^{-1}(0,\epsilon^{-1})$ and the *negative half* to be the
region $s_N^{-1} (-\epsilon^{-1},0)$. For any other fraction, e.g.,
the left-hand three-quarters, the right-hand one-quarter, there are
analogous notions, all measured with respect to $s_N\colon N\to
(-\epsilon^{-1},\epsilon^{-1})$. We also use the terminology the
middle one-half, or middle one-third of the $\epsilon$-neck; again
these regions have their obvious meaning when measured via $s_N$.

*An $\epsilon$-neck* in a Riemannian manifold $X$ is a
codimension-zero submanifold $N$ and an $\epsilon$-structure on $N$
centered at some point $x\in N$.

The *scale* of an $\epsilon$-neck $N$ centered
at $x$ is $R(x)^{-1/2}$. The scale of $N$ is denoted $r_N$. Intuitively, this
is a measure of the radius of the cross-sectional $S^2$ in the neck. In fact,
the extrinsic diameter of any $S^2$ factor in the neck is close to $\sqrt{2}\pi
r_N$. See Fig. 0.1 in the introduction.
