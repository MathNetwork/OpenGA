---
confidence: 0.72
edgeClass: semantic
evidence:
  anaphoraTriggers:
  - context: statement
    direction: previous
    phrase: previous definition
    sort: definition
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 43506
      file: bddcurvbdddist.tex
      sourceTransform: tex2mdx.strip_comments
      start: 43487
    via: local-anaphora-statement
  sourceStatement:
    chapter: 10
    file: bddcurvbdddist.tex
    label: thetaconv
    mtref: '10.21'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 44375
      sourceTransform: tex2mdx.strip_comments
      start: 43422
  targetStatement:
    chapter: 10
    file: bddcurvbdddist.tex
    label: defntheta
    mtref: '10.20'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 43420
      sourceTransform: tex2mdx.strip_comments
      start: 42950
  type: local-anaphora-reference
  via:
  - local-anaphora-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- 5b34d0c84cbb
- f4ee075394ef
rel: depends
reviewStatus: accepted
scope: local-context
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- local-anaphora-statement
---
Morgan--Tian local anaphora dependency.