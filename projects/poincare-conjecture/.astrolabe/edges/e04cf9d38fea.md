---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: shortpi2triv
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 65069
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 65051
    sentence: 'Then using Lemma~\ref{shortpi2triv} and Claim~\ref{vclaim}, we fix
      $\zeta$ with $0<\zeta<\eta/2$ such that: \begin{enumerate} \item[(i)] If $\Gamma\colon
      S^2\to \Lambda {\mathcal X}(t_1)$ is a family of loops and each loop in the
      family is of length less than $\zeta$, then the family is homotopically trivial.
      \item[(ii)] For any $a\in [0,W_\xi(t_0)+2\zeta]$ we have $w_a(t_1)<w(t_1)+\eta/2$.
      \end{enumerate}'
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 65443
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 65033
    sourceStrategy: nearest-previous-statement
    via: prose
  - label: shortpi2triv
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 66466
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 66448
    sentence: By Lemma~\ref{shortpi2triv} this implies that $\widetilde\Gamma(t_1)$
      represents the trivial element in $\pi_2(\Lambda{\mathcal X}(t_1))$, which is
      a contradiction.
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 66603
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 66438
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 18
    file: energy1.tex
    label: shlnsharea
    mtref: '18.28'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 62231
      sourceTransform: tex2mdx.strip_comments
      start: 61985
  targetStatement:
    chapter: 18
    file: energy1.tex
    label: shortpi2triv
    mtref: '18.27'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 60569
      sourceTransform: tex2mdx.strip_comments
      start: 60196
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 37b374f0934d
- ed0e92ce8f57
rel: mentions
reviewStatus: candidate
scope: prose
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- prose
---
Morgan--Tian prose mention. The source is the nearest preceding statement in the same chapter segment.