---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 0
    target: 5
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 52501
    file: surgery.tex
    sourceTransform: tex2mdx.strip_comments
    start: 52489
  sourceStatement:
    chapter: 14
    file: surgery.tex
    label: ''
    mtref: '14.12'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 52840
      sourceTransform: tex2mdx.strip_comments
      start: 52271
  targetStatement:
    chapter: 14
    file: surgery.tex
    label: ''
    mtref: '14.1'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 28555
      sourceTransform: tex2mdx.strip_comments
      start: 27727
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 28217
    file: surgery.tex
    sourceTransform: tex2mdx.strip_comments
    start: 28205
  term: initial time
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:initial time
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- cff982ed3611
- 41da6871e864
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:initial time
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.