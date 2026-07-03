---
chapter: '3'
dcref: ch3:2.9
ref:
- 6df06bf3db9e
sort: proposition
source: tex
src: docarmo
title: exp_q is a local diffeomorphism
---
Given $q\in M$, there exists $\varepsilon>0$ such that
$\exp_q:B_\varepsilon(0)\subset T_qM\to M$ is a diffeomorphism of
$B_\varepsilon(0)$ onto an open subset of $M$.
*Proof.* Compute $d(\exp_q)_0$:

$$
d(\exp_q)_0(v)=\frac{d}{dt}\big(\exp_q(tv)\big)\Big|_{t=0}=\frac{d}{dt}\big(\gamma(1,q,tv)\big)\Big|_{t=0}=\frac{d}{dt}\big(\gamma(t,q,v)\big)\Big|_{t=0}=v.
$$

Hence $d(\exp_q)_0=\mathrm{Id}$ on $T_qM$, and by the inverse function theorem
$\exp_q$ is a local diffeomorphism on a neighborhood of $0$. $\square$