---
confidence: 0.85
edgeClass: semantic
evidence:
  containmentReason: target theorem-like statement occurs inside source proof
  proofSpan:
    bodyEnd: 137790
    bodyStart: 127828
    coordinateSpace: comment-stripped-tex
    depth: 1
    end: 137801
    file: temp2kappa.tex
    ownerLabel: ''
    sourceTransform: tex2mdx.strip_comments
    start: 127815
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: proposition
    mtref: '9.65'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 127812
      sourceTransform: tex2mdx.strip_comments
      start: 127549
  targetStatement:
    chapter: 9
    file: temp2kappa.tex
    label: 2Rbound
    mtref: '9.66'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 128756
      sourceTransform: tex2mdx.strip_comments
      start: 128570
  type: proof-contained-theorem-like-statement
  via:
  - proof-contained-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- ee314aacd207
- ea9b285e40cb
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