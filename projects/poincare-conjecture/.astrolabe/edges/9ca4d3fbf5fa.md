---
confidence: 1.0
edgeClass: semantic
evidence:
  refTriggers:
  - context: statement
    label: lowerbdd
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 41852
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 41838
    via: statement
  - context: proof
    label: lowerbdd
    proofSpan:
      bodyEnd: 42448
      bodyStart: 41878
      coordinateSpace: comment-stripped-tex
      depth: 1
      end: 42459
      file: temp2kappa.tex
      ownerLabel: ''
      sourceTransform: tex2mdx.strip_comments
      start: 41865
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 42001
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 41987
    via: proof
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: ''
    mtref: '9.26'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 41863
      sourceTransform: tex2mdx.strip_comments
      start: 41621
  targetStatement:
    chapter: 9
    file: temp2kappa.tex
    label: lowerbdd
    mtref: '9.25'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 36672
      sourceTransform: tex2mdx.strip_comments
      start: 36453
  type: tex-reference
  via:
  - proof
  - statement
generator: tools/poincare_tex_extract.py
inference: explicit
kind: reference
ref:
- d16f43d74c54
- a6ee3b2ab615
rel: references
reviewStatus: accepted
scope: statement-or-proof
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- proof
- statement
---
Morgan--Tian cross-reference.