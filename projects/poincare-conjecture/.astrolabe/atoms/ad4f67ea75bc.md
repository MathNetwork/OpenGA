---
chapter: 16
generator: tools/poincare_tex_extract.py
label: altern
labels:
- altern
mtref: '16.5'
ref:
- ad4f67ea75bc
sort: proposition
source: tex
src: morgan-tian
tex_file: surgery
---
Given $A<\infty$, $\delta''>0$ and $0<\theta<1$, there is
$\delta''_0=\delta''_0(A,\theta,\delta'')$ ($\delta_0''$ also
depends on $r_{i+1}$, $C$, and $\epsilon$, which are all now fixed)
such that the following holds. Suppose that $({\mathcal M},G)$ is a
Ricci flow with surgery defined for $0\le t<T$ with surgery control
parameter $\overline\delta(t)$. Suppose that it satisfies the strong
$(C,\epsilon)$-canonical neighborhood assumption at all points $x$
with $R(x)\ge r_{i+1}^{-2}$. Suppose also that $({\mathcal M},G)$ has
curvature that is pinched toward positive. Suppose that there is a
surgery at some time $\bar t$ with $T_{i-1}\le \bar t<T$ with $\bar
h$ as the surgery scale parameter. Set $T'=\mathit{min}(T,\bar t+\theta
\bar h^2)$. Let $p\in M_{\bar t}$ be the tip of the cap of a surgery
disk. Then, provided that $\bar\delta(\bar t)\le \delta''_0$ one of
the following holds:

- **(a)** There is an embedding $\rho\colon B(p,\bar t,A\bar h)\times [\bar t,T')\to {\mathcal M}$
compatible with time and the vector field. Let $g'(t),\ \bar t\le
t<T'$, be the one-parameter family of metrics on $B(p,\bar t,A\bar
h)$ given by $\rho^*G$. Shifting this family by $-\bar t$ to make
the initial time $0$ and scaling it by $(\bar h)^{-2}$ produces a
family of metrics $g(t),\ 0\le t<\mathit{min}((T-\bar t)\bar
h^{-2},\theta)$, on $B_{g}(p,0,A)$ that are within $\delta''$ in the
$C^{[1/\delta'']}$-topology of the standard flow on the ball of
radius $A$ at time $0$ centered at the tip of its cap.
- **(b)** There is $\bar t_+\in (\bar t,T')$ and an embedding
$B(p,\bar t,A\bar h)\times [\bar t,\bar t_+)\to {\mathcal M}$
compatible with time and the vector field so that the previous item
holds with $\bar t_+$ replacing $T'$. Furthermore, for any $t<\bar
t_+$ but sufficiently close to $\bar t_+$ the image of $B(p,\bar
t,A\bar h)\times\{t\}$ is contained in the region $D_{t}\subset M_t$
that disappears at time $\bar t_+$.

See Fig. 16.1.
