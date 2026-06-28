---
confidence: 0.9
edgeClass: structural
evidence:
  containmentDepth: 1
  proofSpan:
    bodyEnd: 229182
    bodyStart: 185422
    coordinateSpace: comment-stripped-tex
    depth: 1
    end: 229193
    file: surgery.tex
    ownerLabel: ''
    sourceTransform: tex2mdx.strip_comments
    start: 185409
  sourceStatement:
    chapter: 17
    file: surgery.tex
    label: extend
    mtref: '17.1'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 185406
      sourceTransform: tex2mdx.strip_comments
      start: 184285
  targetContainedSpan:
    coordinateSpace: comment-stripped-tex
    end: 220771
    file: surgery.tex
    sourceTransform: tex2mdx.strip_comments
    start: 220446
  targetStatement:
    chapter: 17
    file: surgery.tex
    label: D(A)delta(A)
    mtref: '17.9'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 220771
      sourceTransform: tex2mdx.strip_comments
      start: 220446
  type: proof-containment
  via:
  - proof-contains
generator: tools/poincare_tex_extract.py
inference: structural
kind: containment
ref:
- 254e8dae97e6
- 7549bace9302
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