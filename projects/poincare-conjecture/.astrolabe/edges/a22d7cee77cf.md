---
confidence: 0.9
edgeClass: structural
evidence:
  containmentDepth: 1
  proofSpan:
    bodyEnd: 123626
    bodyStart: 120090
    coordinateSpace: comment-stripped-tex
    depth: 1
    end: 123637
    file: temp2kappa.tex
    ownerLabel: ''
    sourceTransform: tex2mdx.strip_comments
    start: 120077
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: volcomp
    mtref: '9.60'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 120074
      sourceTransform: tex2mdx.strip_comments
      start: 119331
  targetContainedSpan:
    coordinateSpace: comment-stripped-tex
    end: 121789
    file: temp2kappa.tex
    sourceTransform: tex2mdx.strip_comments
    start: 121292
  targetStatement:
    chapter: 9
    file: temp2kappa.tex
    label: ''
    mtref: '9.61'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 121789
      sourceTransform: tex2mdx.strip_comments
      start: 121292
  type: proof-containment
  via:
  - proof-contains
generator: tools/poincare_tex_extract.py
inference: structural
kind: containment
ref:
- 5cfd7c3aee29
- d2259da4d67d
rel: contains
reviewStatus: accepted
scope: proof
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- proof-contains
---
Morgan--Tian proof containment. The source is the statement whose proof contains the target statement.