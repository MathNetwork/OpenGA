---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: flatssplit
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 99556
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 99540
    sentence: By Claim~\ref{flatssplit} $M$ has either a one- or $2$-sheeted covering
      $\widetilde M$ such that $(\widetilde M,\tilde G(t))$ is a metric product of
      a surface and a one-manifold for all $t<0$
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 99722
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 99530
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: ''
    mtref: '9.51'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 94920
      sourceTransform: tex2mdx.strip_comments
      start: 94840
  targetStatement:
    chapter: 9
    file: temp2kappa.tex
    label: flatssplit
    mtref: '9.45'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 81068
      sourceTransform: tex2mdx.strip_comments
      start: 80573
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 07605ec62528
- afc86a351f0c
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