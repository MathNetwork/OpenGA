---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: Theorem1
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 22234
      file: intro.tex
      sourceTransform: tex2mdx.strip_comments
      start: 22220
    sentence: Rather, we content ourselves with presenting a proof of Theorem~\ref{Theorem1}
      above which, as we have indicated, concerns initial Riemannian manifolds for
      which the Ricci flow with surgery becomes extinct after finite time
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 22379
      file: intro.tex
      sourceTransform: tex2mdx.strip_comments
      start: 22155
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 0
    file: intro.tex
    label: ''
    mtref: '0.6'
    sort: remark
    span:
      coordinateSpace: comment-stripped-tex
      end: 19243
      sourceTransform: tex2mdx.strip_comments
      start: 16436
  targetStatement:
    chapter: 0
    file: intro.tex
    label: Theorem1
    mtref: '0.1'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 2955
      sourceTransform: tex2mdx.strip_comments
      start: 2574
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 48f3d2b5dea3
- 9999efa2be2c
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