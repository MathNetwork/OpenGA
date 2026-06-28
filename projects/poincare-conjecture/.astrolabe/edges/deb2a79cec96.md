---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: bcbd
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 64369
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 64359
    sentence: For all such $\epsilon$, Theorem~\ref{bcbd} holds for $\epsilon$ and
      Proposition~\ref{narrows}, Proposition~\ref{canonvary} and Corollaries~\ref{kappacannbhd}
      and~\ref{limitcannbhd} and Theorems~\ref{smlmtflow} and~\ref{kaplimit} hold
      for $2\epsilon$
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 64577
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 64325
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
    chapter: 10
    file: bddcurvbdddist.tex
    label: bcbd
    mtref: '10.2'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 2942
      sourceTransform: tex2mdx.strip_comments
      start: 2168
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- a992d6a89479
- ecd62fc2ea2b
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