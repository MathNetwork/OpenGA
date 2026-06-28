---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: THM
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 183056
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 183047
    sentence: It now follows from Theorem~\ref{THM} that there is $\kappa>0$ depending
      only on $\kappa_i$, $r'$, $\epsilon$ and $L$ such that $x$ is $\kappa$ non-collapsed
      on scales $\le \epsilon$
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 183201
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 183018
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 16
    file: surgery.tex
    label: ''
    mtref: '16.28'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 176062
      sourceTransform: tex2mdx.strip_comments
      start: 175778
  targetStatement:
    chapter: 8
    file: noncoll.tex
    label: THM
    mtref: '8.1'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 1970
      sourceTransform: tex2mdx.strip_comments
      start: 682
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 3e9580da0ff5
- 3defa9b2209c
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