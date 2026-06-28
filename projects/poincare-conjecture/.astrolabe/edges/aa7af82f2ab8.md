---
confidence: 0.85
edgeClass: semantic
evidence:
  containmentReason: target theorem-like statement occurs inside source proof
  proofSpan:
    bodyEnd: 89985
    bodyStart: 86085
    coordinateSpace: comment-stripped-tex
    depth: 1
    end: 89996
    file: stdsoln.tex
    ownerLabel: ''
    sourceTransform: tex2mdx.strip_comments
    start: 86072
  sourceStatement:
    chapter: 12
    file: stdsoln.tex
    label: ''
    mtref: '12.29'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 86070
      sourceTransform: tex2mdx.strip_comments
      start: 86020
  targetStatement:
    chapter: 12
    file: stdsoln.tex
    label: ''
    mtref: '12.30'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 88901
      sourceTransform: tex2mdx.strip_comments
      start: 88738
  type: proof-contained-theorem-like-statement
  via:
  - proof-contained-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- 729d9a0428c4
- cf6eed7b1da4
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