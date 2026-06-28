---
confidence: 1.0
edgeClass: semantic
evidence:
  refTriggers:
  - context: statement
    label: corequiv
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 12255
      file: intro.tex
      sourceTransform: tex2mdx.strip_comments
      start: 12241
    via: statement
  sourceStatement:
    chapter: 0
    file: intro.tex
    label: finiteext
    mtref: '0.4'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 12644
      sourceTransform: tex2mdx.strip_comments
      start: 11822
  targetStatement:
    chapter: 0
    file: intro.tex
    label: corequiv
    mtref: '0.5'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 14939
      sourceTransform: tex2mdx.strip_comments
      start: 13757
  type: tex-reference
  via:
  - statement
generator: tools/poincare_tex_extract.py
inference: explicit
kind: reference
ref:
- 127db1dc9315
- 7078952cb9e4
rel: references
reviewStatus: accepted
scope: statement-or-proof
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- statement
---
Morgan--Tian cross-reference.