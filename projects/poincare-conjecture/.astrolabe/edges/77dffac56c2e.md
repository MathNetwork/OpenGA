---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: basicconv
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 25124
      file: bddcurvbdddist.tex
      sourceTransform: tex2mdx.strip_comments
      start: 25109
    sentence: Now invoking Theorem~\ref{basicconv} we see that after passing to a
      subsequence we have a geometric limit $(U_\infty,g_\infty,z_\infty)$ of a subsequence
      of $(U_n,g'_n,z'_n)$.
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 25263
      file: bddcurvbdddist.tex
      sourceTransform: tex2mdx.strip_comments
      start: 25087
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 10
    file: bddcurvbdddist.tex
    label: ''
    mtref: '10.6'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 21531
      sourceTransform: tex2mdx.strip_comments
      start: 21390
  targetStatement:
    chapter: 5
    file: converge2.tex
    label: basicconv
    mtref: '5.6'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 9928
      sourceTransform: tex2mdx.strip_comments
      start: 8668
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 6a13c64a90e4
- 74c7682a68ed
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