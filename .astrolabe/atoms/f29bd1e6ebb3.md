---
chapter: '3'
dcref: ch3:3.7
ref:
- f29bd1e6ebb3
sort: theorem
source: tex
src: docarmo
title: totally normal neighborhood
---
For any $p\in M$ there exist a neighborhood $W$ of $p$ and a number $\delta>0$
such that for every $q\in W$, $\exp_q$ is a diffeomorphism on
$B_\delta(0)\subset T_qM$ and $\exp_q(B_\delta(0))\supset W$; that is, $W$ is a
normal neighborhood of each of its points.
*Proof.* Let $\varepsilon$, $V$, $\mathcal{U}$ be as in \entryref{6b083d8aac49}, with
$\mathcal{U}\subset TU$, $V\subset\mathbf{x}(U)$. Define $F:\mathcal{U}\to M\times M$
by $F(q,v)=(q,\exp_q v)$. Around $F(p,0)=(p,p)$ take coordinates
$(U\times U;\mathbf{x},\mathbf{x})$; then since $(d\exp_p)_0=I$,

$$
dF_{(p,0)}=\begin{pmatrix}I & I\\ 0 & I\end{pmatrix},
$$

so $F$ is a local diffeomorphism near $(p,0)$, mapping a neighborhood
$\mathcal{U}'=\{(q,v);\ q\in V',\ v\in T_qM,\ |v|<\delta\}$ diffeomorphically onto
a neighborhood $W'$ of $(p,p)$. Choose $W\ni p$ with $W\times W\subset W'$. For
$q\in W$ and $B_\delta(0)\subset T_qM$, $F(\{q\}\times B_\delta(0))\supset\{q\}\times W$,
so by definition of $F$, $\exp_q(B_\delta(0))\supset W$. $\square$