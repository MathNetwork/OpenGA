---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: fullmeasure
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 182746
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 182729
    sentence: Then, by Corollary~\ref{fullmeasure} (see also, Proposition~\ref{lips}),
      the intersection, $B'$, of ${\mathcal U}_x$ with $B(y,t'',r')$ is an open subset
      of full measure in $B(y,t'',r')$. Of course, ${\rm Vol}\,B'={\rm Vol}\,B(y,t'',r')\ge
      \kappa_i(r')^3$ and the function $l_x$ is bounded by $L/2$ on $B'$
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 183017
      file: surgery.tex
      sourceTransform: tex2mdx.strip_comments
      start: 182709
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
    chapter: 6
    file: newcompar.tex
    label: fullmeasure
    mtref: '6.67'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 101253
      sourceTransform: tex2mdx.strip_comments
      start: 100568
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 3e9580da0ff5
- 7aad50e49af2
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