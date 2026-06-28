---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: stdinit
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 97944
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 97931
    sentence: 'Notice that for the standard initial metric constructed in Lemma~\ref{stdinit}
      we have the following:'
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 97967
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 97865
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 12
    file: stdsoln.tex
    label: stdsolnlimit
    mtref: '12.36'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 97509
      sourceTransform: tex2mdx.strip_comments
      start: 96488
  targetStatement:
    chapter: 12
    file: stdsoln.tex
    label: stdinit
    mtref: '12.2'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 2328
      sourceTransform: tex2mdx.strip_comments
      start: 2256
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 096bebd3ecff
- f1d3021d32b8
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