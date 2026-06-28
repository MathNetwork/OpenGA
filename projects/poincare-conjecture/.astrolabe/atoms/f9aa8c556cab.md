---
chapter: 12
generator: tools/poincare_tex_extract.py
labels: []
mtref: '12.10'
ref:
- f9aa8c556cab
sort: remark
source: tex
src: morgan-tian
tex_file: stdsoln
---
The covariant derivative acts on one-forms $\omega$ in such a way
that the following equation holds:

$$
\langle\nabla(\omega),\xi\rangle=\langle
\omega,\nabla(\xi)\rangle
$$

 for every vector field $\xi$. This means
that in local coordinates we have

$$
\nabla_{\partial_r}(dx^k)=-\Gamma_{rl}^kdx^l.
$$

 Similarly, the Riemann
curvature acts on one-forms $\omega$ satisfying

$$
\mathit{Rm}(\xi_1,\xi_2)(\omega)(\xi)=-\omega\left(\mathit{Rm}(\xi_1,\xi_2)(\xi)\right).
$$

Recall that in local coordinates

$$
R_{ijkl}=\langle \mathit{Rm}(\partial_i,\partial_j)(\partial_l),\partial_k\rangle.
$$

 Thus, we
have

$$
\mathit{Rm}(\partial_i,\partial_j)(dx^k)=-g^{ka}R_{ijal}dx^l=-{{R_{ij}}^k}_ldx^l,
$$

where as usual we use the inverse metric tensor to raise the index.

Also, notice that $\Delta X_{i}-\mathit{Ric}_{ik}X^{k}=-\Delta_{d}X_{i\text{ }}$, where by $\Delta_d$ we
mean the Laplacian associated to the operator $d$ from vector fields
to one-forms with values in the vector field. Since

$$
\begin{aligned}
-\left(  d\delta+\delta d\right)  X_{i}
&  =-\nabla_{i}\left(  -\nabla^{k}X_{k}\right)  -\left(
-\nabla^{k}\right)
\left(  \nabla_{k}X_{i}-\nabla_{i}X_{k}\right) \\
&
=\nabla_{i}\nabla^{k}X_{k}+\nabla^{k}\nabla_{k}X_{i}-\nabla^{k}\nabla
_{i}X_{k}\\
&  ={{{R_{i}}^k}_k}^jX_{j}+\nabla^{k}\nabla_{k}X_{i}=\Delta
X_{i}-\mathit{Ric}_i^jX_{j}.
\end{aligned}
$$
