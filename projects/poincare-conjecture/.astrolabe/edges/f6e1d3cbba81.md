---
confidence: 0.72
edgeClass: semantic
evidence:
  anaphoraTriggers:
  - context: proof
    direction: previous
    phrase: previous lemma
    proofSpan:
      bodyEnd: 169692
      bodyStart: 163171
      coordinateSpace: comment-stripped-tex
      depth: 1
      end: 169703
      file: temp2kappa.tex
      ownerLabel: ''
      sourceTransform: tex2mdx.strip_comments
      start: 163158
    sort: lemma
    sourceSpan:
      coordinateSpace: comment-stripped-tex
      end: 164905
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 164891
    via: local-anaphora-proof
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: ''
    mtref: '9.86'
    sort: remark
    span:
      coordinateSpace: comment-stripped-tex
      end: 163155
      sourceTransform: tex2mdx.strip_comments
      start: 163012
  targetStatement:
    chapter: 9
    file: temp2kappa.tex
    label: ''
    mtref: '9.84'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 159621
      sourceTransform: tex2mdx.strip_comments
      start: 158978
  type: local-anaphora-reference
  via:
  - local-anaphora-proof
generator: tools/poincare_tex_extract.py
inference: inferred
kind: dependency
ref:
- 51da06702a9f
- 6bda3981dbaa
rel: depends
reviewStatus: accepted
scope: local-context
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- local-anaphora-proof
---
Morgan--Tian local anaphora dependency.