---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: A_0
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 64095
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 64086
    sentence: We fix $0<\epsilon\le {\rm min}(1/200,\left(\sqrt{D}(A_0+5)\right)^{-1},\bar\epsilon_1/2,\bar
      \epsilon'/2,\epsilon_0)$ where $\bar\epsilon_1$ is the constant from Proposition~\ref{narrows},
      $\bar\epsilon'$ is the constant from Theorem~\ref{kappasummary}, $\epsilon_0$
      is the constant from Section~\ref{10.1}, and $A_0$ and $D$ are the constants
      from Lemma~\ref{A_0}. We fix $\beta<1/2$, the constant from Proposition~\ref{neckglue}
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 64162
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 63728
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 15
    file: surgery.tex
    label: neckglue
    mtref: '15.2'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 61465
      sourceTransform: tex2mdx.strip_comments
      start: 60812
  targetStatement:
    chapter: 12
    file: stdsoln.tex
    label: A_0
    mtref: '12.3'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 6040
      sourceTransform: tex2mdx.strip_comments
      start: 5568
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- a992d6a89479
- 0b07beec84c0
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