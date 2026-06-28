---
confidence: 0.85
edgeClass: semantic
evidence:
  containmentReason: target theorem-like statement occurs inside source proof
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
  type: proof-contained-theorem-like-statement
  via:
  - proof-contained-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- 5cfd7c3aee29
- d2259da4d67d
rel: depends
reviewStatus: accepted
scope: proof-containment
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- proof-contained-statement
---
Morgan--Tian proof-contained statement dependency.