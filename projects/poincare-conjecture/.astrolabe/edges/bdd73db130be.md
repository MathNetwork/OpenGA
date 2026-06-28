---
confidence: 0.85
edgeClass: semantic
evidence:
  containmentReason: target theorem-like statement occurs inside source proof
  proofSpan:
    bodyEnd: 14349
    bodyStart: 5983
    coordinateSpace: comment-stripped-tex
    depth: 3
    end: 14360
    file: noncoll.tex
    ownerLabel: small
    sourceTransform: tex2mdx.strip_comments
    start: 5970
  sourceStatement:
    chapter: 8
    file: noncoll.tex
    label: small
    mtref: '8.3'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 5471
      sourceTransform: tex2mdx.strip_comments
      start: 5161
  targetStatement:
    chapter: 8
    file: noncoll.tex
    label: nabR
    mtref: '8.5'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 6558
      sourceTransform: tex2mdx.strip_comments
      start: 6089
  type: proof-contained-theorem-like-statement
  via:
  - proof-contained-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- 26e1a6292fef
- bf8f356cfd7a
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