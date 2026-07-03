---
chapter: '3'
dcref: ch3:3.5
ref:
- fa0c59ada60c
sort: lemma
source: tex
src: docarmo
title: Gauss
---
Let $p\in M$ and $v\in T_pM$ with $\exp_p v$ defined, and $w\in T_pM\approx T_v(T_pM)$.
Then

$$
\langle(d\exp_p)_v(v),\,(d\exp_p)_v(w)\rangle=\langle v,w\rangle.\qquad\text{(2)}
$$

*Proof.* Write $w=w_T+w_N$, $w_T$ parallel to $v$, $w_N$ normal to $v$. Since
$d\exp_p$ is linear and
$\langle(d\exp_p)_v(v),(d\exp_p)_v(w_T)\rangle=\langle v,w_T\rangle$, it suffices
to prove (2) for $w=w_N$ ($w_N\ne 0$). Pick a curve $v(s)$ in $T_pM$ with
$v(0)=v$, $v'(0)=w_N$, $|v(s)|=\text{const}$. Since $\exp_p v$ is defined,
choose $\varepsilon>0$ so that $\exp_p(tv(s))$ is defined for $0\le t\le 1$,
$|s|<\varepsilon$, and consider the parametrized surface
$f(t,s)=\exp_p tv(s)$ whose curves $t\mapsto f(t,s_0)$ are geodesics.
Then $\langle\frac{\partial f}{\partial s},\frac{\partial f}{\partial t}\rangle(1,0)=\langle(d\exp_p)_v(w_N),(d\exp_p)_v(v)\rangle$.
Since $\frac{\partial f}{\partial t}$ is the tangent of a geodesic and by symmetry
of the connection,

$$
\frac{\partial}{\partial t}\Big\langle\frac{\partial f}{\partial s},\frac{\partial f}{\partial t}\Big\rangle=\Big\langle\frac{D}{\partial t}\frac{\partial f}{\partial s},\frac{\partial f}{\partial t}\Big\rangle=\Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle=\frac12\frac{\partial}{\partial s}\Big\langle\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle=0,
$$

so $\langle\frac{\partial f}{\partial s},\frac{\partial f}{\partial t}\rangle$ is
independent of $t$. As $\lim_{t\to0}\frac{\partial f}{\partial s}(t,0)=\lim_{t\to0}(d\exp_p)_{tv}\,t w_N=0$,
the inner product is $0$, proving (2). $\square$
