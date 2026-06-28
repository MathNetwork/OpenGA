---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: shiw/deriv
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 17587
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 17571
    sentence: Furthermore, for each $R<\infty$ there is a uniform $C^\infty$ point-wise
      bound to the curvatures of $g_0$ restricted to the images of the $\psi_k$ for
      $k\ge k_0(R)$. Since the flow $g(t)$ has bounded curvature on $\Ar^3\times [0,T']$,
      it follows from Theorem~\ref{shiw/deriv} that there are uniform $C^\infty$ point-wise
      bounds for the curvatures of $g(t)$ restricted to $\psi_k(S^2\times (-R,R))$
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 17709
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 17309
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 12
    file: stdsoln.tex
    label: third
    mtref: '12.6'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 12060
      sourceTransform: tex2mdx.strip_comments
      start: 11922
  targetStatement:
    chapter: 3
    file: flowbasics.tex
    label: shiw/deriv
    mtref: '3.29'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 42464
      sourceTransform: tex2mdx.strip_comments
      start: 41312
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 2e8c17743da6
- e0b6a1f646a7
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