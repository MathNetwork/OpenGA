---
confidence: 0.85
edgeClass: semantic
evidence:
  containmentReason: target theorem-like statement occurs inside source proof
  proofSpan:
    bodyEnd: 28148
    bodyStart: 26997
    coordinateSpace: comment-stripped-tex
    depth: 1
    end: 28159
    file: newcompar.tex
    ownerLabel: ''
    sourceTransform: tex2mdx.strip_comments
    start: 26984
  sourceStatement:
    chapter: 6
    file: newcompar.tex
    label: DLJacobi
    mtref: '6.19'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 26981
      sourceTransform: tex2mdx.strip_comments
      start: 26317
  targetStatement:
    chapter: 6
    file: newcompar.tex
    label: ''
    mtref: '6.20'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 27985
      sourceTransform: tex2mdx.strip_comments
      start: 27774
  type: proof-contained-theorem-like-statement
  via:
  - proof-contained-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- d2e61ac52277
- da7306fc733d
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