---
confidence: 1.0
edgeClass: semantic
evidence:
  refTriggers:
  - context: statement
    label: GSSclass
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 103853
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 103839
    via: statement
  - context: proof
    label: GSSclass
    proofSpan:
      bodyEnd: 105941
      bodyStart: 103880
      coordinateSpace: comment-stripped-tex
      depth: 1
      end: 105952
      file: temp2kappa.tex
      ownerLabel: ''
      sourceTransform: tex2mdx.strip_comments
      start: 103867
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 105048
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 105034
    via: proof
  - context: proof
    label: GSSclass
    proofSpan:
      bodyEnd: 105941
      bodyStart: 103880
      coordinateSpace: comment-stripped-tex
      depth: 1
      end: 105952
      file: temp2kappa.tex
      ownerLabel: ''
      sourceTransform: tex2mdx.strip_comments
      start: 103867
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 105467
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 105453
    via: proof
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: ''
    mtref: '9.54'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 103864
      sourceTransform: tex2mdx.strip_comments
      start: 103562
  targetStatement:
    chapter: 9
    file: temp2kappa.tex
    label: GSSclass
    mtref: '9.42'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 75321
      sourceTransform: tex2mdx.strip_comments
      start: 74299
  type: tex-reference
  via:
  - proof
  - statement
generator: tools/poincare_tex_extract.py
inference: explicit
kind: reference
ref:
- 92ee3ee82b58
- 2d68880771ff
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