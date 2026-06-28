---
confidence: 0.85
edgeClass: semantic
evidence:
  containmentReason: target theorem-like statement occurs inside source proof
  proofSpan:
    bodyEnd: 54967
    bodyStart: 37263
    coordinateSpace: comment-stripped-tex
    depth: 1
    end: 54978
    file: energy1.tex
    ownerLabel: W_2
    sourceTransform: tex2mdx.strip_comments
    start: 37250
  sourceStatement:
    chapter: 18
    file: energy1.tex
    label: W_2
    mtref: '18.11'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 36484
      sourceTransform: tex2mdx.strip_comments
      start: 36186
  targetStatement:
    chapter: 18
    file: energy1.tex
    label: ''
    mtref: '18.16'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 47275
      sourceTransform: tex2mdx.strip_comments
      start: 47013
  type: proof-contained-theorem-like-statement
  via:
  - proof-contained-statement
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- 7bb0fa0c9412
- 39199318fe64
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