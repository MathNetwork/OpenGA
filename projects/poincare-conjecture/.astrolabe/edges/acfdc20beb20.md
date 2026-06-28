---
confidence: 0.85
edgeClass: semantic
evidence:
  containmentReason: target theorem-like statement occurs inside source proof
  proofSpan:
    bodyEnd: 173338
    bodyStart: 165469
    coordinateSpace: comment-stripped-tex
    depth: 1
    end: 173349
    file: surgery.tex
    ownerLabel: delta0ri+1
    sourceTransform: tex2mdx.strip_comments
    start: 165456
  sourceStatement:
    chapter: 16
    file: surgery.tex
    label: delta0ri+1
    mtref: '16.4'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 109162
      sourceTransform: tex2mdx.strip_comments
      start: 107682
  targetStatement:
    chapter: 16
    file: surgery.tex
    label: lvalue
    mtref: '16.26'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 171497
      sourceTransform: tex2mdx.strip_comments
      start: 171318
  type: proof-contained-theorem-like-statement
  via:
  - proof-contained-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- 89a60eb69c3f
- 8cae73a6a02c
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