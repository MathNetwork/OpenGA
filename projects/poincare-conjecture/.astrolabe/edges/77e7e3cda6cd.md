---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: 4picase
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 63741
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 63728
    sentence: According to Theorem~\ref{4picase} this implies that $\widetilde V_\infty(\tau)=(4\pi)^{n/2}$
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 63800
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 63706
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: ''
    mtref: '9.36'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 62699
      sourceTransform: tex2mdx.strip_comments
      start: 62344
  targetStatement:
    chapter: 7
    file: newcomp2.tex
    label: 4picase
    mtref: '7.27'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 48373
      sourceTransform: tex2mdx.strip_comments
      start: 47991
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 64100c8689ff
- 613fb3994956
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