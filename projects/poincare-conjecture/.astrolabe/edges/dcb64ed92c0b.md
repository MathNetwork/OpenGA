---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 0
    target: 2
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 35252
    file: newcompar.tex
    sourceTransform: tex2mdx.strip_comments
    start: 35222
  sourceStatement:
    chapter: 6
    file: newcompar.tex
    label: injdefn
    mtref: '6.25'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 35883
      sourceTransform: tex2mdx.strip_comments
      start: 34564
  targetStatement:
    chapter: 6
    file: newcompar.tex
    label: ''
    mtref: '6.1'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 3679
      sourceTransform: tex2mdx.strip_comments
      start: 3370
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 3552
    file: newcompar.tex
    sourceTransform: tex2mdx.strip_comments
    start: 3522
  term: parameterized by backward time
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:parameterized by backward time
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- 90fe97584bdd
- 6a961a764f44
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:parameterized by backward time
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.