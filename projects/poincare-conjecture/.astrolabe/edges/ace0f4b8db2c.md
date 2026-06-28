---
confidence: 1.0
edgeClass: semantic
evidence:
  refTriggers:
  - context: statement
    label: stdsolncannbhd
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 96600
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 96580
    via: statement
  - context: proof
    label: stdsolncannbhd
    proofSpan:
      bodyEnd: 97617
      bodyStart: 97524
      coordinateSpace: comment-stripped-tex
      depth: 1
      end: 97628
      file: stdsoln.tex
      ownerLabel: ''
      sourceTransform: tex2mdx.strip_comments
      start: 97511
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 97583
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 97563
    via: proof
  sourceStatement:
    chapter: 12
    file: stdsoln.tex
    label: stdsolnlimit
    mtref: '12.36'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 97509
      sourceTransform: tex2mdx.strip_comments
      start: 96488
  targetStatement:
    chapter: 12
    file: stdsoln.tex
    label: stdsolncannbhd
    mtref: '12.32'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 94479
      sourceTransform: tex2mdx.strip_comments
      start: 93886
  type: tex-reference
  via:
  - proof
  - statement
generator: tools/poincare_tex_extract.py
inference: explicit
kind: reference
ref:
- 096bebd3ecff
- 6ff28dba4e56
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