---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: lipaty
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 97615
      file: newcompar.tex
      sourceTransform: tex2mdx.strip_comments
      start: 97603
    sentence: In order to complete the proof of Proposition~\ref{lipaty} we must establish
      inequalities in the opposite direction
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 97672
      file: newcompar.tex
      sourceTransform: tex2mdx.strip_comments
      start: 97556
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 6
    file: newcompar.tex
    label: ''
    mtref: '6.64'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 96436
      sourceTransform: tex2mdx.strip_comments
      start: 96257
  targetStatement:
    chapter: 6
    file: newcompar.tex
    label: lipaty
    mtref: '6.59'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 87473
      sourceTransform: tex2mdx.strip_comments
      start: 86282
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 30414a5a14a9
- 96ced8c484df
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